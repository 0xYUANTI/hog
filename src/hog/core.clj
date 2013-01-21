;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hog - A simple, probabilistic, parallel SAT solver.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_* Declarations =====================================================
(ns hog.core
  (:use clojure.test)
  (:use slingshot.slingshot)
  (:use clojure.set))

(declare normalize search)
(declare L plus minus Cl)
(declare prepare initialize satisfied? wsat)
(declare eval-clause eval-literal)
(declare flip-random flip-greedy flip do-flip)
(declare best score sat-count sat-split)

;;;_* Code =============================================================
;;;_ * API -------------------------------------------------------------
(defn solve
  "Attempt to satisfy a given propositional formula.
   The input is the ``obvious'' sexp-encoding of propositional logic.
   Supported connectives include `and', `or', `not', `->' (implies), and
   `<->' (equivalent). `and' and `or' take any number of arguments.
   Variables are named by symbols.
   The output is a satisfying assignment (a map from variable names to
   truth values) if one could be found or nil if not.
   Note that Hog is incomplete, so a return value of nil does _not_
   imply that no such assignment exists."
  [a]
  (search (normalize a)))

;;;_ * Internals -------------------------------------------------------
;;;_  * Lib ------------------------------------------------------------
(defn all
  "True iff PRED holds for all elements of XS."
  [pred xs] (nil? (filter (complement pred) xs)))

(defn flatmap
  "Map F over XS, then flatten the result."
  [f xs] (flatten (map f xs)))

(defn member?
  "True iff X is an element of XS."
  [x xs] (some #(= % x) xs))

(defn zip
  "A seq of pairs of corresponding elements from XS and YS."
  [xs ys] (map vector xs ys))

;;;_  * CNF conversion -------------------------------------------------
;;;_   * Combined ------------------------------------------------------
(defn- normalize
  "Convert A to conjunctive normal form.
   We apply the structure-preserving transformation first, then convert
   the resulting clauses to CNF using the standard method.
   The output is a seq of seqs. We drop tautologies and duplicate
   variables."
  [a]
  (let [La (L a)] ;must be evaluated first due to side-effects in L
    (cons La (mapcat Cl (seq (plus a))))))

(deftest normalize-test
  (testing "http://en.wikipedia.org/wiki/Tseitin-Transformation"
    (is (= '([]) (normalize '(and a b))))
    (is (= '([]) (normalize '(not (and a b)))))
    (is (= '([]) (normalize '(or a b))))
    (is (= '([]) (normalize '(not (or a b)))))
    (is (= '([]) (normalize '(not a))))
    (is (= '([]) (normalize '(or (and a (not b)) (and (not a) b)))))
    (is (= '([]) (normalize '(or (or (and (not x1) x2)
                                     (and x1 (not x2)))
                                 (and (not x2) x3)))))))

;;;_   * Syntax --------------------------------------------------------
;; Trees:
(def op   first)
(def args rest)
(def arg1 #(nth % 2))
(def arg2 #(nth % 3))
(def arg3 #(nth % 4))

(def leaf? symbol?)
(def node? list?)


;; Recursion:
(defn- treemap [f tree] (cons (op tree) (map f (args tree))))


;; Make tree-pattern matching a bit easier.
(defmacro treecase [tree & clauses]
  `(case (if (leaf? ~tree) '~'leaf (op ~tree))
     ~@clauses))

(deftest treecase-test
  (let [f (fn [a]
            (treecase a
              leaf 0
              and  1
              2))]
    (is (= 0 (f 'a)))
    (is (= 1 (f '(and a b))))
    (is (= 2 (f '(or a b))))))


;; Make a choice.
(defn- treepick [tree x]
  (let [[matching rest] (split-with #(and (seq %) (= (op %) x)) tree)]
    (when (seq matching)
      [(first matching) (concat (rest matching) rest)])))

(deftest treepick-test
  (= ['(and b c) '((and e f) a d)]
     (treepick '(or a (and b c) d (and e f)) 'and)))


;; ...and some helpers.
(defn- literal? [a]
  (treecase a
    leaf true
    not  (treecase (arg1 a)
           leaf true
           false)
    false))

(defn- clause? [a]
  (treecase a
    or (all literal? a)
    false))

(deftest clause?-test
  (= true  (clause? '(or a b (not c))))
  (= false (clause? '(or a b (not (and c d))))))

;;;_   * Standard ------------------------------------------------------
;; Textbook CNF via de Morgan's law, double negation, the law of
;; distribution, and the standard definitions of implication and
;; equivalence.
(defn- rewrite
  "Express implication and equivalence in terms of simpler connectives."
  [a]
  (treecase a
    leaf a
    <->  (rewrite `(and (-> ~(arg1 a) ~(arg2 a))
                        (-> ~(arg2 a) ~(arg1 a))))
    ->   (rewrite `(or (not ~(arg1 a))
                       ~(arg2 a)))
    (treemap rewrite a)))

(deftest rewrite-test
  (is (= '(and (or (not (and a b)) (and b a))
               (or (not (and b a)) (and a b)))
         (rewrite '(<-> (and a b) (and b a))))))


(defn- negate [a]
  (treecase a
    not (arg1 a)
    `(not ~a)))

(defn- nnf
  "Compute the Negation Normal Form of A."
  [a]
  (treecase a
    leaf a
    not  (let [b (arg1 a)]
           (treecase b
             leaf a
             not  (nnf (arg1 b))
             and  (nnf `(or  ~@(map negate (args b))))
             or   (nnf `(and ~@(map negate (args b))))))
    (treemap nnf a)))

(deftest nnf-test
  (is (= 'a                            (nnf 'a)))
  (is (= '(not a)                      (nnf '(not a))))
  (is (= 'a                            (nnf '(not (not a)))))
  (is (= '(and a b)                    (nnf '(and a b))))
  (is (= '(or (not a) (and b (not c))) (nnf '(not (and a (or (not b) c)))))))


(defn- cnf
  "Translate a formula in NNF to CNF."
  [a]
  (treecase a
    leaf a
    not  a
    or   (if-let [[conj rest] (treepick a 'and)]
           (cnf `(and ~@(map #(`(or ~% ~@rest)) (args conj))))
           (treemap cnf a))
    and  (treemap cnf a)))

(deftest cnf-test
  (is (= '(and a b)               (cnf '(and a b))))
  (is (= '(or a b)                (cnf '(or a b))))
  (is (= '(and (or a c) (or b c)) (cnf '(or (and a b) c)))))


(defn- simplify
  "Move ops upwards in the tree."
  [a]
  (treecase a
    leaf a
    not  a
    or   (if-let [[disj rest] (treepick a 'or)]
           (simplify `(or ~@disj ~@rest))
           (treemap simplify a))
    and  (if-let [[conj rest] (treepick a 'and)]
           (simplify `(and ~@conj ~@rest))
           (treemap simplify a))))

(deftest simplify-test
  (is (= '(and (or a b) (or b c) (or c d))
         (simplify '(and (and (or a b) (and (or b c) (or c d))))))))


(defn- tautology? [a]
  (or (member? (negate (first a)) (rest a))
      (recur (rest a))))

(defn- minimize [a] (if (tautology? a) nil (distinct a)))

(defn- compress
  "Drop superfluous literals and clauses, and implicit connectives."
  [a]
  (treecase a
    leaf a
    not  a
    or   (list (minimize (rest a)))
    and  (map (comp minimize rest) (rest a))))

(deftest compress-test
  (is (= '((a b) (c (not d)))
         (minimize '(and (or a a b)
                         (or (not c) c a b)
                         (or c (not d) (not d)))))))


;; We have:
(defn- Cl [a]
  (-> a
      rewrite
      nnf
      cnf
      simplify
      compress))

(deftest Cl-test
  (testing "http://en.wikipedia.org/wiki/Conjunctive_normal_form"
    (is (= (Cl '(and (not a) (or b c)))
           '([(not a)] [b c])))
    (is (= (Cl '(and (or a b) (or (not b) c (not d)) (or d (not e))))
           '([a b] [(not b) c (not d)] [d (not e)])))
    (is (= (Cl '(or a b))
           '([a b])))
    (is (= (Cl '(and a b))
           '([a] [b])))
    (is (= (Cl '(not (or b c)))
           '([(not b)]  [(not c)])))
    (is (= (Cl '(or (and a b) c))
           '([a c] [b c])))
    (is (= (Cl '(and a (or b (and d e))))
           '([a] [b d] [b e])))))

;;;_   * Structure-preserving ------------------------------------------
;; The transformation described in Plaisted & Greenbaum, 1986 (adapted
;; to propositional logic).
(def n (ref -1))

(defn- gen! []
  (dosync (alter n inc))
  (symbol (str "P" @n)))

(defn- reset-counter! [] (dosync (alter n (fn [_] -1))))


(def L
  ;; Ensure multiple occurences of the same subformula are associated
  ;; with the same predicate symbol!
  (memoize
   (fn [a]
     (treecase a
       leaf a
       not  `(not (L (arg1 a)))
       (gen!)))))

(def plus
  ;; Must be memoized for complexity bounds to hold.
  (memoize
   (fn [a]
     (treecase a
       leaf #{}
       and  (union #{`(-> ~(L a) (and ~@(map L (args a))))}
                   (apply union (map plus (args a))))
       or   (if (clause? a)
              #{`(-> ~(L a) ~a)}
              (union #{`(-> ~(L a) (or ~@(map L (args a))))}
                     (apply union (map plus (args a)))))
       not  (minus (arg1 a))
       <->  (union #{`(-> ~(L a) (<-> ~(L (arg1 a)) ~(L (arg2 a))))}
                   (plus (arg1 a))
                   (plus (arg2 a))
                   (minus (arg1 a))
                   (minus (arg2 a)))
       ->   (union #{`(-> ~(L a) (-> ~(L (arg1 a)) ~(L (arg2 a))))}
                   (minus (arg1 a))
                   (plus (arg2 a)))))))

(def minus
  ;; Must be memoized for complexity bounds to hold.
  (memoize
   (fn [a]
     (treecase a
       leaf #{}
       and  (union #{`(-> (and ~@(map L (args a))) ~(L a))}
                   (apply union (map minus (args a))))
       or   (if (clause? a)
              #{`(-> ~a ~(L a))}
              (union #{`(-> (or ~@(map L (args a))) ~(L a))}
                     (apply union (map minus (args a)))))
       not  (plus (arg1 a))
       <->  (union #{`(-> (<-> ~(L (arg1 a)) ~(L (arg2 a))) ~(L a))}
                   (minus (arg1 a))
                   (minus (arg2 a))
                   (plus (arg1 a))
                   (plus (arg2 a)))
       ->  (union #{`(-> (-> ~(L (arg1 a)) ~(L (arg2 a))) ~(L a))}
                  (plus (arg1 a))
                  (minus (arg2 a)))))))

(deftest structure-preserving-test
  (testing "http://dl.acm.org/citation.cfm?id=7244"
    ;; (= (plus '(or (and q1 q2) (and q3 q4)))
    ;;    #{(-> r1 (or r2 r3))
    ;;      (-> r2 (and q1 q2))
    ;;      (-> r3 (and q3 q4))})
    ;; (= (normalize '(or (and q1 q2) (and q3 q4)))
    ;;    #{(or (not r1) r2 r3)
    ;;      (or (not r2) q1)
    ;;      (or (not r2) q2)
    ;;      (or (not r3) q3)
    ;;      (or (not r3) q4)
    ;;      (or (not r4) q4)})
    ;; (= (plus '(or (and q1 q2) (not (and q3 q4))))
    ;;    #{(-> r1 (or r2 (not r3)))
    ;;      (-> r2 (and q1 q2))
    ;;      (-> (and q3 q4) r3)})

    ;; (let [b2 '(and d1 d2 d3 d4)
    ;;       a  `(and (or c1 c2) (-> (or c2 c1) ~b2) (not ~b2))]
    ;;   (= (Cl )
    ;;      )
    ;;   (= (plus )
    ;;      )
    ;;   (= (normalize )
    ;;      ))
    ))

;;;_  * Proof search ---------------------------------------------------
;;;_   * Loop ----------------------------------------------------------
(defrecord Result [t])

(defn- search
  "Try to find a satisfying assignment for CNF formula A."
  ([a]
     (solve a 100 1000 0.5 2))
  ([a max-cores]
     (solve a 100 1000 0.5 max-cores))
  ([a max-tries max-flips p]
     (let [a (prepare a)]
       (try+
        (loop [i max-tries]
          (let [a (initialize a)]
            (loop [a a j max-flips]
              (if (satisfied? a)
                (throw+ (Result. (:t a)))
                (recur (wsat a p) (- j 1)))))
          (recur (- i 1)))
        (catch Result res (:t res)))))
  ([a max-tries max-flips p max-cores]
     (let [p (promise)]
       (dotimes [i max-cores]
         (println "starting thread " i)
         (future (deliver p (search a max-tries max-flips p))))
       (deref p)         ;block
       (shutdown-agents) ;kill other futures
       (deref p))))      ;cheap

(deftest search-test
  (search '())
  (search '([]))
  (search '([a] [b]))
  (search '([a b] [(not a) (not b)])))

;;;_   * Data ----------------------------------------------------------
;; Our input is a formula, which is a seq of clauses, which are seqs of
;; literals, which are either plain or negated variables.
(defn- variable [lit] (if (symbol? lit) lit (second lit)))

;; We precompute all queries against the input formula, collect the
;; results in a map, and use that internally.
(defn- clause
  "Index lookup."
  [a idx] (get-in a [:idx->clause idx]))

(defn- idx
  "Reverse index lookup."
  [a clause] (get-in a [:clause->idx clause]))

(defn- clauses
  "All clauses in which VAR occurs."
  [a var] (get-in a [:var->clauses var]))

(defn- idxs
  "The indices of all clauses in which VAR occurs."
  [a var] (get-in a [:var->idxs var]))

(defn- vars
  "All variables which occur in the clause indexed by IDX."
  [a idx] (get-in a [:idx->vars idx]))

;; The main integer-to-clause index is just a vector of the input
;; formula. All derived indices are computed using the following
;; functional.
(defn- reindex [f index]
  (reduce-kv (fn [acc idx clause]
               (reduce (fn [acc lit]
                         (let [[k v] (f idx clause (variable lit))]
                           (update-in acc [k] (partial cons v))))
                       acc
                       clause))
             {}
             index))

(defn- prepare
  "Precompute some useful indices."
  [a]
  (let [idx->clause (vec a)]
    {:raw          a
     :idx->clause  idx->clause
     :clause->idx  (zipmap a (range (count a)))
     :var->clauses (reindex (fn [_   clause var] [var clause]) idx->clause)
     :var->idxs    (reindex (fn [idx _      var] [var idx])    idx->clause)
     :idx->vars    (reindex (fn [idx _      var] [idx var])    idx->clause)}))

(deftest prepare-test
  (let [a (prepare '([a b c] [(not a) b] [(not c) b]))]
    (is (= '([a b c] [(not a) b]) (clauses a 'a)))
    (is (= '(0 1 2)               (idxs a 'b)))
    (is (= '(a b)                 (vars a 1)))))


;; We also need a work list and the current assignment.
(defn- sat-clauses
  "The clauses satisfied by A's current assignment."
  [a] (a :sat))

(defn- unsat-clauses
  "The clauses not satisfied by A's current assignment."
  [a] (a :unsat))

(defn- assignment
  "A's current assignment."
  [a] (a :t))

;; Generate assignments:
(defn- rand-bool [] (case (rand-int 0 2) 0 false 1 true))

(defn- fresh-assignment
  "A random truth assignment for VARS. Assignments are mappings from
   variable-symbols to booleans."
  [vars] (reduce (fn [acc var] (assoc acc var (rand-bool))) {} vars))

;; Derive a subset of entries from an index:
(defn- subindex [pred? index]
  (set (flatmap (fn [[k v]] (if (pred? k) v nil)) index)))

(defn- initialize
  "(Re)initialize A with a fresh assignment."
  [a]
  (let [t (fresh-assignment (keys (a :var->clauses)))]
    (assoc a
      :t     t
      :sat   (subindex #(eval-clause % t)       (a :clause->idx))
      :unsat (subindex #(not (eval-clause % t)) (a :clause->idx)))))

(deftest initialize-test
  (let [a (initialize (prepare '([a])))]
    (case (get-in a [:t 'a])
      true  (is (= #{} (unsat-clauses a)))
      false (is (= #{} (sat-clauses a))))))


;; Clauses are evaluated with respect to some assignment.
(defn- eval-clause
  "Is CLAUSE satisfied by T?"
  [clause t]
  (if (nil? clause)
    true
    (or (eval-literal (first clause) t) (eval-clause (rest clause) t))))

(defn- eval-literal [lit t] (if (symbol? lit) (t lit) (not (t (second lit)))))

(deftest eval-test
  (= true  (eval-clause '(a b)       {'a true 'b true}))
  (= false (eval-clause '((not a) b) {'a true 'b true})))

;;;_   * Step ----------------------------------------------------------
(defn- satisfied? [a] (nil? (seq (unsat-clauses a))))

(defn- wsat
  "Flip a single variable. First, pick a random unsatisfied clause.
   Then, either greedily or randomly pick a variable from that clause
   to flip."
  [a p]
  (let [idx (rand-nth (seq (unsat-clauses a)))]
    (if (<= (rand) p)
      (flip-random a idx)
      (flip-greedy a idx))))

(defn- flip-random [a idx] (flip a (rand-nth (vars a idx))))

(defn- flip-greedy [a idx] (flip a (best (vars a idx)) a))


(defn- best [vars a] (second (first (sort-by first (map #(score % a) vars)))))

(defn- score
  "Assign a score to VAR based on the decrease in the total number of
   unsatisfied clauses caused by flipping it."
  [var a]
  (let [clauses (clauses a var)
        t       (assignment a)
        sat0    (sat-count clauses t)
        sat1    (sat-count clauses (do-flip t var))]
    [(- sat1 sat0) var]))

(defn- sat-count [clauses t]
  (reduce (fn [acc c] (if (eval-clause c t) (inc acc) acc)) 0 clauses))

(deftest best-test
  (let [a (initialize (prepare '([a])))]
    (is (= 'a (best (vars a 0) a)))))


(defn- flip [a var]
  (let [clauses     (zip (idxs a var) (clauses a var))
        t           (do-flip (a :t) var)
        old-sat     (a :sat)
        old-unsat   (a :unsat)
        [sat unsat] (sat-split clauses t)]
    (assoc a
      :t     t
      :sat   (union (difference old-sat unsat) sat)
      :unsat (union (difference old-unsat sat) unsat))))

(defn- do-flip [t var] (assoc t var (not (t var))))

(defn- sat-split [clauses t]
  (reduce (fn [[sat unsat] [i c]]
            (if (eval-clause c t)
              [(conj i sat) unsat]
              [sat (conj i unsat)]))
          [#{} #{}]
          clauses))

(deftest flip-test
  (let [a  (initialize (prepare '([a])))
        a' (flip a 'a)]
    (is (= (sat-clauses a) (unsat-clauses a')))
    (is (= (unsat-clauses a) (sat-clauses a')))))

;;;_* Emacs ============================================================
;;; Local Variables:
;;; allout-layout: t
;;; End:
