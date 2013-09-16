(ns optimizer.core
  (:refer-clojure :exclude (complement))
  (:use midje.sweet)
  (:require [clojure.core.match :as m :refer (match)]
            [clojure.math.combinatorics :as math]))

;; Okay, let's get our grammar worked out. We're parsing expressions
;; that look like:
;;
;; (and (or v0 v1) v2)

(def prefixes
  "The set of valid variable prefixes."
  #{\v \w})

(def prefix
  "Returns the supplied symbol's first character."
  (comp first name))

;; Variable validation

(def literals #{'T 'F})
(def literal? (comp boolean literals))

(defn variable? [x]
  (and (symbol? x)
       (contains? prefixes (prefix x))))

(defn cheap? [x]
  (and (variable? x) (= \v (prefix x))))

(defn expensive? [x]
  (and (variable? x) (= \w (prefix x))))

;; Variable Creation

(defn cheap [n]
  (symbol (str \v n)))

(defn expensive [n]
  (symbol (str \w n)))

;; Expression Validation

(defn unary? [exp]
  (and (coll? exp)
       (= 2 (count exp))))

(defn binary? [exp]
  (and (coll? exp)
       (= 3 (count exp))))

(defn func
  "Returns the function of the supplied boolean expression."
  [exp] (first exp))

(defn arguments
  "Returns the arguments of the supplied boolean expression."
  [exp] (rest exp))

(defn conjunction?
  "Returns true if the supplied expression is of the form
  (and <variable> <variable>), false otherwise."
  [exp]
  (and (binary? exp)
       (= 'and (func exp))))

(defn conjunction [a b] (list 'and a b))

(defn disjunction?
  "Returns true if the supplied expression is of the form
  (or <variable> <variable>), false otherwise."
  [exp]
  (and (binary? exp)
       (= 'or (func exp))))

(defn disjunction [a b] (list 'or a b))

(defn negation?
  "Returns true if the supplied expression is of the form
  (not <variable>), false otherwise."
  [exp]
  (and (unary? exp)
       (= 'not (func exp))))

(defn negation [x] (list 'not x))

(defn complement
  "If x is a negation, returns its argument, else returns the negation
  of x."
  [x]
  (if (negation? x)
    (first (arguments x))
    (negation x)))

(def expression?
  "Returns true if the supplied expression is a valid boolean
  expression, false otherwise."
  (some-fn conjunction? disjunction? negation?))

(defn make-checker
  ([pred] (make-checker pred (fn [_] false)))
  ([pred else]
     (fn recurse [exp]
       (boolean
        (cond (or (pred exp) (literal? exp)) true
              (expression? exp) (every? recurse (arguments exp))
              :else (else exp))))))

(def valid?
  "Returns true if the supplied expression is a valid boolean
  expression, false otherwise. The test is applie recursively down to
  all subforms."
  (make-checker
   variable?
   #(println "Subexpression is invalid: " %)))

(def fully-cheap?
  "Returns true if the supplied expression contains only cheap
  variables, false otherwise."
  (make-checker cheap?))

(let [mixed-exp '(and (or w1 v1) v2)]
  (fact
    (conjunction (disjunction (expensive 1)
                              (cheap 1))
                 (cheap 2))
    => mixed-exp)
  (fact
    mixed-exp =not=> fully-cheap?
    mixed-exp => valid?))

;; Great, so now we have this form validator and some ways to build
;; and deconstruct algebraic expressions.

(defn fixed-point [f guess]
  (let [next (f guess)]
    (if (= guess next)
      next
      (fixed-point f next))))

(defn eq
  "Equality for boolean expressions."
  [x y]
  (if (and (expression? x) (expression? y))
    (and (= (func x) (func y))
         (let [[lx ly] (arguments x)
               [rx ry] (arguments y)]
           (or (and (eq lx rx) (eq ly ry))
               (and (eq lx ry) (eq ly rx)))))
    (= x y)))

(defn switch-or
  "returns true if the supplied binary pred returns true when passed x
  and y in either order."
  [pred x y]
  (boolean
   (or (pred x y)
       (pred y x))))

(defn complement-law [x y]
  (and (negation? x)
       (eq (complement x) y)))

;; There are a few laws we ALWAYS want to apply.
;;
;; * Involution Law: (not (not a)) == a
;;
;; * Identity Laws: (and a F) == F, (and a T) == a, (or a F) == a,
;;   (or a T) == T
;;
;; * Idempotent Laws: (or a a) == a, (and a a) == a
;;
;; * Complement Laws: (and a (not a)) == F, (or a (not a)) == T, (not
;;F) == T, (not T) == F

(defmacro expmatch [v & forms]
  `(let [v# ~v]
     (if-not (expression? v#)
       v#
       (match (vec v#) ~@forms))))

(defn simplify [exp]
  (letfn [(bool-reduce [e]
            (expmatch e
                      ;; Identity Laws
                      ['and x 'F] 'F
                      ['and 'F x] 'F
                      ['or x 'T] 'T
                      ['or 'T x] 'T
                      ['not 'T] 'F
                      ['not 'F] 'T
                      ['and x 'T] x
                      ['and 'T x] x
                      ['or x 'F] x
                      ['or 'F x] x
                      ;; DeMorgan's Laws (unwrapping)
                      [(:or 'and 'or) (l :guard negation?) (r :guard negation?)]
                      (let [f (if (= (func e) 'and)
                                conjunction
                                disjunction)]
                        (negation
                         (f (complement l)
                            (complement r))))
                      [(:or 'and 'or) x y]
                      (let [f (func e)
                            x (simplify x)
                            y (simplify y)]
                        (cond (eq x y) x ;; Idempotent Laws
                              ;; Complement Laws
                              (switch-or complement-law x y)
                              (if (conjunction? e) 'F 'T)
                              ;; Else, sub in new, reduced arguments
                              :else (list f x y)))

                      ;; Involution Law
                      ['not (x :guard negation?)] (complement x)
                      ['not x] (negation (simplify x))
                      :else e))]
    (fixed-point bool-reduce exp)))

(let [example-expression '(or (and (and v1 (or v2 v3)) (not w1)) F)]
  (fact
    "Reduce away the or F:"
    (simplify example-expression) => '(and (and v1 (or v2 v3)) (not w1))

    "and F == F"
    (simplify '(and (and (and v1 (or v2 v3)) (not w1)) F)) => 'F

    "No reduction..."
    (simplify '(and (or w1 v1) v2)) => '(and (or w1 v1) v2)

    "(or a a) => a"
    (simplify '(and (or w1 w1) v2)) => '(and w1 v2)))

;; The next laws serve to give me different permutations on the
;; original input expression.

(defmacro matcher [& pairs]
  `(fn [exp#]
     (if-not (expression? exp#)
       []
       (match (vec exp#)
              ~@pairs
              :else []))))

(def demorgan
  (matcher
   ;; DeMorgan's Laws (conjunctions)
   ['not (([_ l r] :seq) :guard conjunction?)]
   [(conjunction (negation l)
                 (negation r))]

   ['and (l :guard negation?) (r :guard negation?)]
   [(negation
     (conjunction (complement l)
                  (complement r)))]

   ;; DeMorgan's Laws (disjunctions)
   ['not (([_ l r] :seq) :guard disjunction?)]
   [(disjunction (negation l)
                 (negation r))]

   ['or (l :guard negation?) (r :guard negation?)]
   [(negation
     (disjunction (complement l)
                  (complement r)))]))

(def associative
  (matcher
   ;; Associative Laws (conjunctions)
   ['and (([_ a b] :seq) :guard conjunction?) c]
   [(conjunction a (conjunction b c))]

   ['and a (([_ b c] :seq) :guard conjunction?)]
   [(conjunction (conjunction a b) c)]

   ;; Associative Laws (disjunctions)
   ['or (([_ a b] :seq) :guard disjunction?) c]
   [(disjunction a (disjunction b c))]

   ['or a (([_ b c] :seq) :guard disjunction?)]
   [(disjunction (disjunction a b) c)]))

(def distributive
  (matcher
   ;; Distributive Laws
   ['and
    (([_ a b] :seq) :guard disjunction?)
    (([_ c d] :seq) :guard disjunction?)]
   (if (= a c)
     [(disjunction a (conjunction b d))]
     [])

   ['and a (([_ b c] :seq) :guard disjunction?)]
   [(disjunction (conjunction a b)
                 (conjunction a c))]

   ['or
    (([_ a b] :seq) :guard conjunction?)
    (([_ c d] :seq) :guard conjunction?)]
   (if (eq a c)
     [(conjunction a (disjunction b d))]
     [])

   ['or a (([_ b c] :seq) :guard conjunction?)]
   [(conjunction (disjunction a b)
                 (disjunction a c))]))



(comment
  (let [cake (matcher ['and
                       (([_ a b] :seq) :guard disjunction?)
                       (([_ c d] :seq) :guard disjunction?)]
                      [(disjunction a (conjunction b d))])]
    (cake '(and (or 1 2) (or 1 3))))

  (fact
    "DeMorgan's laws:"
    (expand '(not v1)) => ['(not v1)])

  (defn commutative-expand [exp]
    (if-not (expression? exp)
      [exp]
      (match (vec exp)
             ['not a] (map negation (expand a))
             [(:or 'and 'or) ls rs]
             (let [f (func exp)]
               (apply concat
                      (for [l (expand ls)
                            r (expand rs)]
                        [(list f l r) (list f r l)]))))))

  (defn win? [exp]
    (or (cheap? exp)
        (and (expression? exp))
        (match (vec exp)
               ['and l r] (map negation (expand a))
               [(:or 'and 'or) ls rs]
               :else false))))

(defn print-all [xs]
  (doseq [x xs] (println x)))

(tabular
 (fact
   (?op ?x) => [?y]
   (?op ?y) => [?x])
 ?op      ?x                 ?y
 ;; DeMorgan's Laws
 demorgan '(not (and v1 v2)) '(and (not v1) (not v2))
 demorgan '(not (or v1 v2))  '(or (not v1) (not v2)))
