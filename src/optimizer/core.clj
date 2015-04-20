
(ns optimizer.core
  (:require [clojure.core.match :refer [match]]
            [clojure.set :refer [subset? difference]]))

(def prefixes
   "The set of valid variable prefixes."
   #{\v \w})

 (def prefix
   "Returns the supplied symbol's first character."
   (comp first name))

(defn cheap
  "Generates a cheap variable using the supplied number."
  [n]
  (symbol (str \v n)))

(defn expensive
  "Generates an expensive variable using the supplied number."
  [n]
  (symbol (str \w n)))

(def literals #{'T 'F})

(defn variable?
  "Returns true if the argument is a valid cheap or expensive
  variable, false otherwise."
  [x]
  (and (symbol? x)
       (contains? prefixes (prefix x))))

(def literal?
  "Returns true if passed a literal, false otherwise."
  (comp boolean literals))

(defn unary? [exp]
  (and (coll? exp)
       (= 2 (count exp))))

(defn binary? [exp]
  (and (coll? exp)
       (= 3 (count exp))))

(def func
  "Returns the function of the supplied boolean expression."
  first)

(def args
  "Returns the arguments of the supplied boolean expression."
  rest)

(defn AND?
  "Returns true if the supplied expression is of the form
  (and <variable> <variable>), false otherwise."
  [exp]
  (and (binary? exp)
       (= 'and (func exp))))

(defn AND [a b] (list 'and a b))

(defn OR?
  "Returns true if the supplied expression is of the form
  (or <variable> <variable>), false otherwise."
  [exp]
  (and (binary? exp)
       (= 'or (func exp))))

(defn OR [a b] (list 'or a b))

(defn NOT?
  "Returns true if the supplied expression is of the form
  (not <variable>), false otherwise."
  [exp]
  (and (unary? exp)
       (= 'not (func exp))))

(defn NOT
  "If x is a negation, returns its argument, else returns the negation
  of x."
  [x]
  (if (NOT? x)
    (first (args x))
    (list 'not x)))

(def expr?
  "Returns true if the supplied expression is a valid boolean
  expression, false otherwise."
  (some-fn AND? OR? NOT?))

(defn flatten-binary
  "Returns a function that takes a binary expression and flattens it
  down into a variadic version. Returns the arguments to the variadic
  version.

  If the initial expression doesn't pass the checker, returns a
  singleton list with only that element."
  [pred]
  (fn flatten* [e]
    (if-not (pred e)
      [e]
      (mapcat (fn [x]
                (if (pred x)
                  (flatten* x)
                  [x]))
              (rest e)))))

(def flatten-and (flatten-binary AND?))
(def flatten-or (flatten-binary OR?))

(defn op->binary
  "Moves the `op` instances back into binary form. If no ops are
  provided, returns 'T."
  [op]
  (fn [[x & xs]]
    (reduce op (or x 'T) xs)))

(def and->binary (op->binary AND))
(def or->binary (op->binary OR))

(defn combinations
    "Thanks to amalloy: https://gist.github.com/amalloy/1042047"
    [n coll]
    (if (= 1 n)
      (map list coll)
      (lazy-seq
       (when-let [[head & tail] (seq coll)]
         (concat (for [x (combinations (dec n) tail)]
                   (cons head x))
                 (combinations n tail))))))

(defn absorption-law
  "let lawHandled = case `flatten-fn` of
   `flatten-or`  -> p AND (p OR q) == p
   `flatten-and` -> p OR (p AND q) == p

  Absorption law, from: http://www.nayuki.io/page/boolean-algebra-laws

  The input exprs must all be conjunctions if you pass `flatten-or`
  and all disjunctions if you pass `flatten-and`.

  Returns a sequence of simplified conjunctions (or disjunctions)."
  [flatten-fn exprs]
  (let [exprs (set exprs)
        args* (comp set flatten-fn)]
    (->> (for [[l r] (combinations 2 exprs)
               :let [ls (args* l)
                     rs (args* r)]]
           (cond (subset? ls rs) #{r}
                 (subset? rs ls) #{l}
                 :else #{}))
         (reduce into #{})
         (difference exprs)
         (seq))))
(defn simplify-binary
  "Returns a function that simplifies binary expressions.

  Rules handled:

  Annihilator: (p OR T) = T, (p AND F) = F
  Identity:    (p AND T) = p, (p OR F) = p
  Idempotence: (p AND p) = (p OR p) = p (accumulating into a set)
  Complement:  (p AND (NOT p)) = F, (p OR (NOT p)) = T

  The flattening implementation depends on associativity and
  commutativity."
  [{:keys [ctor annihilator id flatten-fn tear-fn]}]
  (let [zip-fn (op->binary ctor)]
    (fn attack
      ([l r] (attack (flatten-fn (ctor l r))))
      ([xs]
       (letfn [(absorb [acc p]
                 (cond (= p id) acc
                       (or (= p annihilator)
                           (acc (NOT p)))
                       (reduced [annihilator])
                       :else (conj acc p)))]
         (->> (reduce absorb #{} xs)
              (absorption-law tear-fn)
              (zip-fn)))))))
(def simplify-and
  "Returns a function that simplifies an AND expression. Returns an
  expression in conjunctive normal form."
  (simplify-binary
   {:ctor AND
    :annihilator 'F
    :id 'T
    :flatten-fn flatten-and
    :tear-fn flatten-or}))
(def simplify-or*
  "Returns a function that simplifies an OR expression."
  (simplify-binary
   {:ctor OR
    :id 'F
    :annihilator 'T
    :flatten-fn flatten-or
    :tear-fn flatten-and}))
(defn simplify-or
  "Applies the distributive law to convert the OR into CNF, then
  applies the AND simplifications."
  [l r]
  (simplify-and
   (for [l (flatten-and l)
         r (flatten-and r)]
     (simplify-or* l r))))
(defn simplify
  "returns a simplified expression in Conjunctive Normal
  Form."
  [exp]
  (match (if (expr? exp) (vec exp) exp)
         ;; AND and OR simplification
         ['and p q] (simplify-and (simplify p) (simplify q))
         ['or  p q] (simplify-or  (simplify p) (simplify q))

         ;; NOT complement laws:
         ['not 'T] 'F
         ['not 'F] 'T

         ;; (NOT (NOT p)) => p (involution law)
         ['not (['not p] :seq)] (simplify p)

         ;; DeMorgan's Laws
         ['not (['and p q] :seq)] (simplify (OR (NOT p) (NOT q)))
         ['not (['or p q] :seq)] (simplify (AND (NOT p) (NOT q)))

         ['not x] (NOT (simplify x))

         ;; Returns constants and literals.
         :else exp))

(defn make-checker
  "Takes a predicate that checks the leaves. Optionally takes an
  `else` function called if an invalid expression is passed in."
  ([pred] (make-checker pred (fn [_] false)))
  ([pred else]
   (fn recurse [exp]
     (boolean
      (cond (or (pred exp) (literal? exp)) true
            (expr? exp) (every? recurse (args exp))
            :else (else exp))))))

(def cheap?
  "Returns true if the supplied expression contains only cheap
  variables, false otherwise."
  (make-checker
   (fn [x]
     (if (variable? x)
       (= \v (prefix x))))))

(def expensive?
  "Returns true if the supplied expression is fully expensive, false
  otherwise."
  (complement cheap?))

(defn pushdown-only [exp]
  (and->binary
   (filter cheap? (flatten-and (simplify exp)))))

(def separate (juxt filter remove))

(defn factor
  "Reverse of the distributive property:

  (and (p or q) (p or z)) = (p or (and q z))"
  [cnf-exp]
  (letfn [(max-factor [ors]
            (->> (apply concat ors)
                 (frequencies)
                 (sort-by (comp - val))
                 (first)))
          (factor* [clauses]
            (let [flat-clauses (map flatten-or clauses)
                  [shared-exp n] (max-factor flat-clauses)]
              (and->binary
               (if (= n 1)
                 clauses
                 (let [factorable? (partial some #{shared-exp})
                       [haves have-nots] (separate factorable? flat-clauses)
                       conjuncts (for [clause haves :when (not= clause [shared-exp])]
                                   (or->binary (remove #{shared-exp} clause)))]
                   ;; If you can't pull the shared expression out of 2
                   ;; or more subexpressions, abort.
                   (if (< (count conjuncts) 2)
                     clauses
                     (let [factored (OR shared-exp (factor* conjuncts))]
                       (if-let [remaining (not-empty (map or->binary have-nots))]
                         [(factor* remaining) factored]
                         [factored]))))))))]
    (factor*
     (flatten-and cnf-exp))))

(def pushdown
  (comp factor pushdown-only))
