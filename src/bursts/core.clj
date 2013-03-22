(ns bursts.core
  (:require [clojure.contrib.profile]))

;; util for clojure array
(defn array? [x] (-> x class .isArray))
(defn see [x] (if (array? x) (map see x) x))

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


(defn min-index
  "returns the index of the minimum number in a vector"
  [coll]
  (first (apply min-key second (map-indexed vector coll))))


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
  (let [
        res (loop [tis (range 0 nb-gaps)
                   costs (into [] (cons 0 (repeat (dec max-states) (Double/POSITIVE_INFINITY))))
                   op-seq (mk-op-seq-init max-states 1)]
              (if (empty? tis)
                {:cost costs
                 :optimal op-seq}
                (let [t-i (first tis)
                      res (loop [js (range 0 max-states)
                                 costs-prime (into [] (repeat max-states (Double/NaN)))
                                 op-seq-prime (mk-op-seq-init max-states (inc t-i))]
                            (if (empty? js)
                              {:cost costs-prime
                               :optimal op-seq-prime}
                              (let [j (first js)
                                    cost (into []
                                               (map (fn [k]
                                                      (+ (nth costs k) (tau k j)))
                                                    (range 0 max-states)))
                                    ell (min-index cost)
                                    costs-prime-j (- (nth cost ell)
                                                     (Math/log (f j (nth gaps t-i))))]

                                (when (> t-i 0)
                                  (let [col (aget op-seq ell)]
                                    (doseq [tt (range 0 t-i)]
                                      (aset op-seq-prime j tt (aget col tt)))))
                                (aset op-seq-prime j t-i j)
                                (recur (rest js)
                                       (assoc costs-prime j costs-prime-j)
                                       op-seq-prime ))))]
                  (recur (rest tis) (:cost res) (:optimal res)))))]
    ;; extract the state sequence with the minimum final cost
    (let [j (min-index (:cost res))]
      (into [] (seq (aget (:optimal res) j))))))


(defn compute-ouput-nb-entries
  "compute the number of entries we will need in the output"
  [op-seq nb-gaps]
  (loop [nb 0
         prev -1
         tis (range 0 nb-gaps)]
    (if (empty? tis)
      nb
      (let [t (first tis)
            op-seq-t (nth op-seq t)
            nb* (if (> op-seq-t prev)
                  (+ nb (- op-seq-t prev))
                  nb)]
        (recur nb* op-seq-t (rest tis))))))

(defn mk-bursts
  "run through the state sequence, and pull out the durations of all the
   intervals for which the system is at or above a given state greater
   than 1. 'track' keeps track of which bursts are currently open"
  [nb-burst opt-seq offsets]
  (let [res
        (loop [tis (range 0  (dec (count offsets)))
               burst-counter -1
               bursts []
               stack-counter -1
               stack (into [] (repeat nb-burst (Double/NaN)))
               prev -1]
          (if (empty? tis)
            [bursts stack-counter stack]
            (let [t (first tis)
                  num-level (Math/abs (- (nth opt-seq t) prev))
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
                (recur (rest tis)
                       (nth res 1)
                       (nth res 0)
                       (nth res 3)
                       (nth res 2)
                       (nth opt-seq t))
                (recur (rest tis)
                       burst-counter
                       bursts
                       stack-counter
                       stack
                       (nth opt-seq t))))))]
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
        ;_ (println "gaps:" gaps)
        sum-gaps (apply + gaps)
        ;_ (println "sum gaps:" sum-gaps)
        nb-gaps (count gaps)
        ;_ (println "nb-gaps:" nb-gaps)
        ghat (/ sum-gaps nb-gaps)
        ;_ (println "ghat:" ghat)
        nb-states-max (upper-bound-of-nb-states gaps sum-gaps scaling)
        ;_ (println "max states:" nb-states-max)
        gamma-logn (* gamma (Math/log nb-gaps))
        ;_ (println gamma-logn)
        tau-f (tau gamma-logn)
        density-f (f (mk-aphas scaling ghat nb-states-max))
        optimal (optimal-state-sequence nb-states-max nb-gaps gaps tau-f density-f)
        ;_ (println "optimal" optimal)
        nb-out-entries (compute-ouput-nb-entries optimal nb-gaps)
        ;_ (println "entries:" nb-out-entries)
        bursts (mk-bursts nb-out-entries optimal offsets)]
    {:burst bursts
     :gaps gaps
     :max-states nb-states-max
     :out-entries nb-out-entries}))

