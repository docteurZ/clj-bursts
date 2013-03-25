(ns bursts.core
  (:require [bursts.util :as arr]))

(defn mk-gaps
  "makes the gaps data  where gaps[t] gives the length of the gap between
  the events at offsets[t] and offsets[t+1]"
  [offsets]
  (let [offsets (sort offsets)
        gaps (into [] (map (fn [[o1 o2]]
                             (- o2 o1))
                           (partition 2 1 offsets)))]
    gaps))

(defn mk-aphas
  [scaling ghat max-states]
  (into []
        (for [x (range 0 max-states)]
          (/ (Math/pow scaling x) ghat))))

(defn log-with-base
  "computes log given a val and a base"
  ([n b]
     (/ (Math/log n) (Math/log b)))
  ([n]
     (log-with-base n (Math/exp 1))))

(defn upper-bound-of-nb-states
  "compute an upper bound on the number of states used in the optimal state
   sequence, as per Kleinberg (theorem p.8)"
  [gaps sum-gaps scaling]
  (let [upper-val (+ 1 (log-with-base sum-gaps scaling)
                     (log-with-base (/ 1 (apply min gaps)) scaling))]
    (Math/ceil upper-val)))


(defn tau
  "transition cost function"
  [gamma-logn]
  (fn
    [i j]
    (if (>= i j)
      0
      (* (- j i) gamma-logn))))


(defn f
  "probability density function for gap lengths when in state j,
   with precomputed parameters"
  [alphas]
  (fn [j x]
    (let [alpha-j (nth alphas j)]
      (* alpha-j (Math/exp (-(* alpha-j x)))))))


(defn mk-op-seq-init
  "init of the optimal sequence"
  [nrows ncols]
  (let [arr (make-array Double/TYPE nrows ncols)]
    (for [i (range 0 nrows)]
      (for [j (range 0 ncols)]
        (aset arr i j (Double/NaN))))
    arr))


(defn optimal-state-sequence
  "compute the optimal state sequence for the model, using the Viterbi
   algorithm. In each iteration t, we compute for each possible state j the
   minimum costs of partial state sequences up to iteration t that end in
   that state. These numbers are stored in 'costs'.  We use 'op-seq' to keep track of
   the optimal sequences for each j."
  [max-states nb-gaps gaps tau f]
  (let [max-states (int max-states)
        nb-gaps (int nb-gaps)
        res (loop [t-i (int 0)
                   costs (into [] (cons 0 (repeat (dec max-states) (Double/POSITIVE_INFINITY))))
                   op-seq (mk-op-seq-init max-states 1)]
              (if (>= t-i nb-gaps)
                {:cost costs
                 :optimal op-seq}
                (let [op-seq-prime (mk-op-seq-init max-states (inc t-i))
                      res (loop [j (int 0)
                                 costs-prime (into [] (repeat max-states (Double/NaN)))
                                 op-seq-prime (mk-op-seq-init max-states (inc t-i))]
                            (if (>= j max-states)
                              {:cost costs-prime
                               :optimal op-seq-prime}
                              (let [cost (into []
                                               (map (fn [k]
                                                      (+ (nth costs k) (tau k j)))
                                                    (range (int 0) max-states)))
                                    ell (arr/min-index cost)
                                    costs-prime-j (- (nth cost ell)
                                                     (Math/log (f j (nth gaps t-i))))]

                                (when (> t-i 0)
                                  (doseq [tt (range 0 t-i)]
                                    (arr/deep-aset doubles op-seq-prime j tt
                                                   (arr/deep-aget doubles op-seq ell tt))))
                                (arr/deep-aset doubles op-seq-prime j t-i j)
                                (recur (inc j)
                                       (assoc costs-prime j costs-prime-j)
                                       op-seq-prime))))]
                  (recur (inc t-i) (:cost res) (:optimal res)))))]
    ;; extract the state sequence with the minimum final cost
    (let [j (arr/min-index (:cost res))]
      (into [] (-> #^objects (:optimal res)
                   (#^doubles aget j)
                   seq)))))


(defn compute-ouput-nb-entries
  "compute the number of entries we will need in the output"
  [op-seq nb-gaps]
  (let [part-states (partition-by identity op-seq)]
    (loop [part-states (partition-by identity op-seq)
           nb (int 0)
           prev (int -1)]
      (if (empty? part-states)
        nb
        (let [val-state (int (first (first part-states)))
              nb* (if (> val-state prev)
                    (+ nb (- val-state prev))
                    nb)]
          (recur (rest part-states) nb* val-state))))))

(defn mk-bursts
  "run through the state sequence, and pull out the durations of all the
   intervals for which the system is at or above a given state greater
   than 1. 'track' keeps track of which bursts are currently open"
  [nb-burst opt-seq offsets]
  (let [t-imax (dec (count offsets))
        res
        (loop [t (int 0)
               burst-counter (int -1)
               bursts []
               stack-counter (int -1)
               stack (into [] (repeat nb-burst (Double/NaN)))
               prev (int -1)]
          (if (>= t t-imax)
            [bursts stack-counter stack]
            (let [num-level (Math/abs (- (int (nth opt-seq t)) prev))
                  levels (range 1 (inc num-level))
                  res (if (> (nth opt-seq t) prev)
                        ;; level opened
                        (loop [levels* levels
                               burst-counter* burst-counter
                               bursts* bursts
                               stack-counter* stack-counter
                               stack* stack]
                          (if (empty? levels*)
                            [bursts* burst-counter* stack* stack-counter*]
                            (let [i (first levels*)
                                  bursts* (conj bursts* {:level (+ prev i)
                                                         :start (nth offsets t)})
                                  burst-counter* (inc burst-counter*)
                                  stack-counter* (inc stack-counter*)]
                              (recur (rest levels*)
                                     burst-counter*
                                     bursts*
                                     stack-counter*
                                     (assoc stack* stack-counter* burst-counter*)))))
                        (when (> num-level 0)
                          ;; level closed
                          (loop [levels* levels
                                 burst-counter* burst-counter
                                 bursts* bursts
                                 stack-counter* stack-counter
                                 stack* stack]
                            (if (empty? levels*)
                              [bursts* burst-counter* stack* stack-counter*]
                              (recur (rest levels*)
                                     burst-counter*
                                     (assoc-in bursts*
                                               [(nth stack* stack-counter) :end]
                                               (nth offsets t))
                                     (dec stack-counter*)
                                     stack*)))))]
              (if res
                (recur (inc t)
                       (int (nth res 1))
                       (nth res 0)
                       (int (nth res 3))
                       (nth res 2)
                       (int (nth opt-seq t)))
                (recur (inc t)
                       burst-counter
                       bursts
                       stack-counter
                       stack
                       (int (nth opt-seq t)))))))]
    ;; end the opened bursts
    (loop [stack-counter* (nth res 1)
           bursts* (nth res 0)]
      (if (<=  stack-counter* -1)
        bursts*
        (recur (dec stack-counter*)
               (assoc-in bursts*
                         [(nth (nth res 2) stack-counter*) :end]
                         (last offsets)))))))

(defn burst-detection
  "This function attempts to identify ‘bursts’ of activity in a series of discrete events
   that take place at known times, based on an inﬁnite hidden Markov model. An optimal state
   sequence is computed that balances the total transition cost against the probability of
   the observed event timing."
  [offsets {:keys [scaling gamma] :or {:scaling 2 :gamma 1}}]
  (let [offsets (into [] (sort offsets))
        gaps (mk-gaps offsets)
        sum-gaps (apply + gaps)
        nb-gaps (count gaps)
        ghat (/ sum-gaps nb-gaps)
        nb-states-max (upper-bound-of-nb-states gaps sum-gaps scaling)
        gamma-logn (* gamma (Math/log nb-gaps))
        tau-f (tau gamma-logn)
        density-f (f (mk-aphas scaling ghat nb-states-max))
        optimal  (optimal-state-sequence nb-states-max nb-gaps gaps tau-f density-f)
        nb-out-entries (compute-ouput-nb-entries optimal nb-gaps)
        bursts (mk-bursts nb-out-entries optimal offsets)]
    {:burst bursts
     :nb-gaps nb-gaps
     :max-states nb-states-max
     :out-entries nb-out-entries}))

