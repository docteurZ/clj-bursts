(ns bursts.util)

(defn min-index
  "returns the index of the minimum number in a vector"
  [coll]
  (first (apply min-key second (map-indexed vector coll))))

;; utilities and macros for clojure multidim array
;; from http://clj-me.cgrand.net/2009/10/15/multidim-arrays/
(defn array? [x] (-> x class .isArray))
(defn see [x] (if (array? x) (map see x) x))

(defmacro deep-aget
  ([hint array idx]
    `(aget ~(vary-meta array assoc :tag hint) ~idx))
  ([hint array idx & idxs]
    `(let [a# (aget ~(vary-meta array assoc :tag 'objects) ~idx)]
       (deep-aget ~hint a# ~@idxs))))

(defmacro deep-aset [hint array & idxsv]
  (let [hints '{doubles double ints int}
        [v idx & sxdi] (reverse idxsv)
        idxs (reverse sxdi)
        v (if-let [h (hints hint)] (list h v) v)
        nested-array (if (seq idxs)
                       `(deep-aget ~'objects ~array ~@idxs)
                        array)
        a-sym (with-meta (gensym "a") {:tag hint})]
      `(let [~a-sym ~nested-array]
         (aset ~a-sym ~idx ~v))))
