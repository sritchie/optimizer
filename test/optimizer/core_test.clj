
(ns optimizer.core-test
  (:use optimizer.core)
  (:require [clojure.core.match :refer [match]]
            [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]))

(def cheap-v (gen/fmap cheap gen/nat))
(def expensive-v (gen/fmap expensive gen/nat))
(def variable (gen/one-of [cheap-v expensive-v]))

(defn tuplefn [g]
  (letfn [(apply-tuple [[op & xs]] (apply op xs))]
    (gen/fmap apply-tuple g)))

(defn nested-binary [f]
  (-> (fn [g]
        (tuplefn
         (gen/tuple (gen/return f) g g)))
      (gen/recursive-gen variable)))

;; Make sure that flatten-and kills all the nested ands.
(defspec flatten-and-spec
  100
  (prop/for-all
   [e (nested-binary AND)]
   (let [flattened (flatten-and e)]
     (and (AND? e)
          (every? variable? flattened)))))

;; Same thing for or:
(defspec flatten-or-spec
  100
  (prop/for-all
   [e (nested-binary OR)]
   (let [flattened (flatten-or e)]
     (and (OR? e) (every? variable? flattened)))))

;; Also check that and->binary reverses flatten-and.
(defspec and->binary-spec
  100
  (prop/for-all
   [e (nested-binary AND)]
   (let [flattened (flatten-and e)]
     (= flattened (flatten-and (and->binary flattened))))))

;; And the same thing for or:
(defspec or->binary-spec
  100
  (prop/for-all
   [e (nested-binary OR)]
   (let [flattened (flatten-or e)]
     (= flattened (flatten-or (or->binary flattened))))))

(def compound
  (fn [g]
    (tuplefn
     (gen/one-of
      [(gen/tuple (gen/elements [AND OR]) g g)
       (gen/tuple (gen/return NOT) g)]))))

(def expr
  "test.check generator for expressions."
  (gen/recursive-gen compound variable))

(defn variables
  "Returns a set of all unique variables in the supplied expression."
  [e]
  (let [e (if (expr? e) (flatten e) [e])]
    (set (filter variable? e))))

(defn sized-expr
  "Takes some limit on the size of the number of variables in the
  generated expression and returns a generator that won't break that
  number."
  [variable-limit]
  (gen/such-that #(< (count (variables %))
                     variable-limit)
                 expr))

;; ### Solver

(defn solve
  "Takes an expression and a map of variables -> boolean value."
  [e m]
  (letfn [(solve* [e]
            (match (if (expr? e) (vec e) e)
                   'T true
                   'F false
                   ['and p q] (and (solve* p) (solve* q))
                   ['or p q] (or (solve* p) (solve* q))
                   ['not p] (not (solve* p))
                   :else (m e)))]
    (solve* e)))

;; Brute force checks of the simplifier.

(defn cartesian-prod
  "Generates the cartesian product of all the input sequences."
  [colls]
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cartesian-prod (rest colls))]
      (cons x more))))

(defn variable-map
  "Returns a sequence of maps of variable -> Boolean assignment. The
  returned number of maps is equal to 2^n, where n is the number of
  variables."
  [vs]
  (let [vs (vec vs)
        c  (count vs)]
    (map (partial zipmap vs)
         (cartesian-prod
          (repeat c [true false])))))

(defn expr-variables
  "Returns a sequence of maps of the variables that appear in any of
  the exprs -> boolean combinations."
  [& exprs]
  (variable-map (mapcat variables exprs)))

(defn equal?
  "Are the two expressions equal for every possible input?"
  [e1 e2]
  (every? (fn [m]
            (= (solve e1 m)
               (solve e2 m)))
          (expr-variables e1 e2)))

;; Simplifiyng an expression yields an expression equal to the
;; original expression.
(defspec simplify-spec
  100
  (prop/for-all
   [e (sized-expr 7)]
   (let [s (simplify e)]
     (equal? e s))))

(defspec factor-spec
  100
  (prop/for-all
   [e (sized-expr 7)]
   (let [s (simplify e)
         f (factor s)]
     (equal? s f))))

;; pushing
(defspec cheap-spec
  100
  (prop/for-all
   [e (gen/such-that expensive? expr)]
   (let [p (pushdown-only e)
         f (factor p)]
     (and (cheap? p)
          (cheap? f)))))

(defspec prefilter-correctness-law
  100
  (prop/for-all
   [e (sized-expr 8)]
   (let [simplified (pushdown e)]
     (every? (fn [m]
               ;; !simplified => !e
               ;; !(!simplified) OR !e
               ;; simplified OR !e
               (or (solve simplified m)
                   (not (solve e m))))
             (expr-variables e simplified)))))

;; ## CNF Checks

(defn cnf-literal? [p]
  (boolean
   (or (variable? p)
       (literal? p)
       (if (NOT? p)
         (cnf-literal?
          (second p))))))

(defn cnf-clause? [p]
  (or (cnf-literal? p)
      (and (OR? p) (every? cnf-clause? (args p)))))

(defn cnf? [p]
  (or (cnf-literal? p)
      (cnf-clause? p)
      (and (AND? p) (every? cnf-clause? (flatten-and p)))))

(defspec cnf-spec
  100
  (prop/for-all [e expr]
                (cnf? (simplify e))))

(def valid?
  "Returns true if the supplied expression is a valid boolean
  expression, false otherwise. The test is applied recursively down to
  all subforms."
  (make-checker
   variable?
   #(println "Subexpression is invalid: " %)))

(deftest needs-name-test
  (let [mixed-exp '(and (or w1 v1) v2)]
    (is (= mixed-exp
           (AND (OR (expensive 1)
                    (cheap 1))
                (cheap 2))))
    (is (not (cheap? mixed-exp)))
    (is (valid? mixed-exp))))

(deftest simplify-tests
  (let [example-expression '(or (and (and v1 (or v2 v3)) (not w1)) F)]
    "Reduce away the or F:"
    (is (equal? example-expression (simplify example-expression)))

    "and F == F"
    (is (equal? 'F '(and (and (and v1 (or v2 v3)) (not w1)) F)))

    "No reduction..."
    (is (equal? '(and (or w1 v1) v2)
                (simplify '(and (or w1 v1) v2))))

    "(or a a) => a"
    (is (equal? '(and w1 v2)
                (simplify '(and (or w1 w1) v2))))))
