(and (not a) (or b c))
(and (and (or a b)
          (or (or (not b) c)
              (not d)))
     (or d (not e)))
(and a b)

;; Because there's only one clause, this is like (and T (or a b))
(or a b)
(not (and b c)) ;; top level negation
(or c (and a b)) ;; and inside or
(defn simplify
  "returns a simplified expression in conjunctive normal
  form."
  [exp]
  (match (if (expr? exp) (vec exp) exp)
         ;; AND and OR simplification
         ['and p q] (simplify-and (simplify p) (simplify q))
         ['or  p q] (simplify-or  (simplify p) (simplify q))

         ;; NOT simplification:
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
