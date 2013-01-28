;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hog - A simple, probabilistic, parallel SAT solver.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_* Declarations =====================================================
(ns hog.core
  (:use clojure.test)
  (:use slingshot.slingshot)
  (:use clojure.set))

(declare normalize search)
(declare L plus minus Cl reset-counter!)
(declare prepare initialize satisfied? wsat assignment do-search)
(declare eval-clause eval-literal)
(declare flip-random flip-greedy flip do-flip)
(declare best score satcount satsplit)
(declare treesort1 treecompare treecompare1 treecompare2 treeorder treerank)

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
  [a] (search (normalize a)))

(deftest solve-test
  (is (= nil (solve '(not (-> (and (-> a b) a) b)))))
  (let [t (solve '(not (and (-> a b) (-> a (not b)))))
        a (t 'a)
        b (t 'b)]
    (is (= a true)
        (or (= b true)
            (= b false)))))

;;;_ * Internals -------------------------------------------------------
;;;_  * Lib ------------------------------------------------------------
(defn all
  "True iff PRED holds for all elements of XS."
  [pred xs]
  (or (empty? xs)
      (and (pred (first xs)) (recur pred (rest xs)))))

(deftest all-test
  (is (= true  (all even? '(0 2))))
  (is (= false (all even? '(1 2)))))


(defn member?
  "True iff X is an element of XS."
  [x xs] (if (some #(= % x) xs) true false))

(deftest member?-test
  (is (= true  (member? #{} '(#{}))))
  (is (= false (member? #{} '()))))


(defn zip
  "A seq of pairs of corresponding elements from XS and YS."
  [xs ys] (map vector xs ys))

(deftest zip-test
  (is (= '([1 2] [3 4]) (zip '(1 3) '(2 4)))))

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
    (cons [La] (mapcat Cl (seq (plus a))))))


(deftest normalize-test
  (testing "http://en.wikipedia.org/wiki/Tseitin-Transformation"
    (reset-counter!)
    (is (= '([P0] [a (not P0)] [b (not P0)])
           (normalize '(and a b))))
    (is (= '([(not P0)] [(not a) (not b) P0])
           (normalize '(not (and a b)))))
    (is (= '([P1] [a b (not P1)])
           (normalize '(or a b))))
    (is (= '([(not P1)] [(not a) P1] [(not b) P1])
           (normalize '(not (or a b)))))
    (is (= '([(not a)])
           (normalize '(not a))))
    (is (= '([P2] [(not a) (not P4)] [b (not P4)] [P3 P4 (not P2)] [a (not P3)] [(not b) (not P3)])
           (normalize '(or (and a (not b)) (and (not a) b)))))
    (is (= '([P5]
             [(not x1) (not P8)] [x2 (not P8)]
             [P6 P7 (not P5)] [P8 P9 (not P6)]
             [(not x2) (not P7)] [x3 (not P7)]
             [x1 (not P9)] [(not x2) (not P9)])
           (normalize '(or (or (and (not x1) x2)
                               (and x1 (not x2)))
                           (and (not x2) x3))))))
  (testing "http://dl.acm.org/citation.cfm?id=7244"
    (reset-counter!)
    (is (= '([P0] [P1 P2 (not P0)] [q3 (not P2)] [q4 (not P2)] [q1 (not P1)] [q2 (not P1)])
           (normalize '(or (and q1 q2) (and q3 q4)))))
    (reset-counter!)
    (let [a '(and (or c1 c2) (-> (or c2 c1) (and d1 d2)) (not (and d2 d1)))]
      ;; (and b1 (-> b1 b2) (not b2))
      (is (= (Cl a)
             '((d1 (not c1))
               (d2 (not c1))
               (d1 (not c2))
               (d2 (not c2))
               (c1 c2)
               ((not d2) (not d1)))
             ))
      (is (= (plus a)
             '#{(-> P0 (and P1 P2 (not P3)))
                (-> P1 (or c1 c2))
                (-> P2 (-> P1 P3))
                (-> P3 (and d1 d2))
                (-> (and d2 d1) P3)
                (-> (or c2 c1) P1)}
             ))
      (is (= (normalize a)
             '([P0]
               ((not d2) (not d1) P3)
               ((not c2) P1)
               ((not c1) P1)
               (c1 c2 (not P1))
               ((not P1) P3 (not P2))
               (d1 (not P3))
               (d2 (not P3))
               (P1 (not P0))
               (P2 (not P0))
               ((not P3) (not P0)))
             )))))

;;;_   * Syntax --------------------------------------------------------
;; Trees:
(def op   first)
(def args rest)
(def arg1 #(nth % 1))
(def arg2 #(nth % 2))
(def arg3 #(nth % 3))

(def leaf? symbol?)
(def node? seq?)

(deftest tree-test
  (let [tree '(and a b c)]
    (is (= 'and     (op tree)))
    (is (= '(a b c) (args tree)))
    (is (= 'a       (arg1 tree)))
    (is (= 'b       (arg2 tree)))
    (is (= 'c       (arg3 tree)))
    (is (= true     (leaf? 'a)))
    (is (= false    (leaf? tree)))
    (is (= false    (node? 'a)))
    (is (= true     (node? tree)))))


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
  (loop [xs  (args tree)
         acc nil]
    (when (seq xs)
      (let [arg (first xs)]
        (if (and (node? arg) (= (op arg) x))
          [arg (concat (reverse acc) (rest xs))]
          (recur (rest xs) (cons arg acc)))))))

(deftest treepick-test
  (is (= ['(and b c) '(a d (and e f))]
         (treepick '(or a (and b c) d (and e f)) 'and)))
  (is (= nil (treepick '(or a b) 'and))))


;; Make memoize work in more cases.
(defn- treetype [a] (if (leaf? a) :leaf :op))

(defn- treesort [a]
  (treecase a
    leaf a
    not  (treemap treesort a)
    and  (treesort1 (treemap treesort a))
    or   (treesort1 (treemap treesort a))
    ->   (treemap treesort a)
    <->  (treesort1 (treemap treesort a))))

(defn- treesort1 [a] (cons (op a) (sort treecompare (args a))))

(defn- treecompare [a b]
  (case [(treetype a) (treetype b)]
    [:leaf :leaf] (compare a b)
    [:leaf :op]   +1
    [:op   :leaf] -1
    [:op   :op]   (treecompare1 a b)))

(defn- treecompare1 [a b]
  (cond (< (treerank a) (treerank b)) -1
        (> (treerank a) (treerank b)) +1
        :else
        (cond (< (count a) (count b)) -1
              (> (count a) (count b)) +1
              :else
              (treecompare2 (args a) (args b)))))

(defn- treecompare2 [args1 args2]
  (cond (nil? args1) -1
        (nil? args2) +1
        :else
        (let [n (treecompare (first args1) (first args2))]
          (if (= n 0)
            (treecompare2 (rest args1) (rest args2))
            n))))

(def treeorder
  {'and 1
   'or  2
   '->  3
   '<-> 4
   'not 5})

(defn- treerank [a] (treeorder (op a)))

(deftest treesort-test
  (is (= '(not (and (and a b)
                    (or (<-> c d) x)
                    (-> b a)
                    y
                    z))
         (treesort '(not (and (-> b a)
                              (and b a)
                              z
                              (or (<-> d c) x)
                              y))))))


;; ...and some helpers.
(defn- literal? [a]
  (treecase a
    leaf true
    not  (treecase (arg1 a)
           leaf true
           false)
    false))

(deftest literal?-test
  (is (= true  (literal? 'a)))
  (is (= true  (literal? '(not a))))
  (is (= false (literal? '(and a b)))))

(defn- clause? [a]
  (treecase a
    or (all literal? (args a))
    false))

(deftest clause?-test
  (is (= true  (clause? '(or a b (not c)))))
  (is (= false (clause? '(or a b (not (and c d)))))))

;;;_   * Standard ------------------------------------------------------
;; Textbook CNF via de Morgan's law, double negation, the law of
;; distribution, and the standard definitions of implication and
;; equivalence.
(defn- rewrite
  "Express implication and equivalence in terms of simpler connectives."
  [a]
  (treecase a
    leaf a
    <->  (rewrite `(~'and (~'-> ~(arg1 a) ~(arg2 a))
                          (~'-> ~(arg2 a) ~(arg1 a))))
    ->   (rewrite `(~'or (~'not ~(arg1 a)) ~(arg2 a)))
    (treemap rewrite a)))

(deftest rewrite-test
  (is (= '(and (or (not (and a b)) (and b a))
               (or (not (and b a)) (and a b)))
         (rewrite '(<-> (and a b) (and b a))))))


(defn- negate [a]
  (treecase a
    not (arg1 a)
    `(~'not ~a)))

(defn- nnf
  "Compute the Negation Normal Form of A."
  [a]
  (treecase a
    leaf a
    not  (let [b (arg1 a)]
           (treecase b
             leaf a
             not  (nnf (arg1 b))
             and  (nnf `(~'or  ~@(map negate (args b))))
             or   (nnf `(~'and ~@(map negate (args b))))))
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
    or   (if-let [[conj other] (treepick a 'and)]
           (cnf `(~'and ~@(map #(concat (list 'or %) other) (args conj))))
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
    or   (if-let [[disj other] (treepick a 'or)]
           (simplify `(~'or ~@(rest disj) ~@other))
           (treemap simplify a))
    and  (if-let [[conj other] (treepick a 'and)]
           (simplify `(~'and ~@(rest conj) ~@other))
           (treemap simplify a))))

(deftest simplify-test
  (is (= '(and (or b c) (or c d) (or a b))
         (simplify '(and (and (or a b) (and (or b c) (or c d)))))))
  (is (= '(and (or d b) (or e b) a)
         (simplify '(and a (and (or d b) (or e b)))))))


(defn- tautology? [a]
  (and (seq a)
       (or (member? (negate (first a)) (rest a))
           (recur (rest a)))))

(defn- minimize [a] (if (tautology? a) nil (list (distinct a))))

(defn- compress
  "Drop superfluous literals and clauses, and implicit connectives."
  [a]
  (treecase a
    leaf a
    not  a
    or   (mapcat minimize (list (rest a)))
    and  (mapcat #(treecase %
                     leaf (list (list %))
                     not  (list (list %))
                     or   (minimize (rest %)))
                  (rest a))))

(deftest compress-test
  (is (= '((a b) (c (not d)) (e) ((not f)))
         (compress '(and (or a a b)
                         (or (not c) c a b)
                         (or c (not d) (not d))
                         e
                         (not f)
                         (or g (not g)))))))


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
           '([(not b)] [(not c)])))
    (is (= (Cl '(or (and a b) c))
           '([a c] [b c])))
    (is (= (Cl '(and a (or b (and d e))))
           '([d b] [e b] [a])))))

;;;_   * Structure-preserving ------------------------------------------
;; The transformation described in Plaisted & Greenbaum, 1986 (adapted
;; to propositional logic).
(def n (ref -1))

(defn- gen! []
  (dosync (alter n inc))
  (symbol (str "P" @n)))

(defn- reset-counter! [] (dosync (alter n (fn [_] -1))))


(def L'
  ;; Ensure multiple occurences of the same subformula are associated
  ;; with the same predicate symbol!
  (memoize
   (fn [a]
     (treecase a
       leaf a
       not  `(~'not ~(L (arg1 a)))
       (gen!)))))

(defn- L [a]
  (L' (treesort a)))

(deftest L-test
  (reset-counter!)
  (is (= 'P0       (L '(and a b))))
  (is (= 'P0       (L '(and b a))))
  (is (= 'P1       (L '(or a b))))
  (is (= 'a        (L 'a)))
  (is (= '(not a)  (L '(not a))))
  (is (= '(not P2) (L '(not (-> a b))))))


(def plus
  ;; Must be memoized for complexity bounds to hold.
  (memoize
   (fn [a]
     (treecase a
       leaf #{}
       and  (union #{`(~'-> ~(L a) (~'and ~@(map L (args a))))}
                   (apply union (map plus (args a))))
       or   (if (clause? a)
              #{`(~'-> ~(L a) ~a)}
              (union #{`(~'-> ~(L a) (~'or ~@(map L (args a))))}
                     (apply union (map plus (args a)))))
       not  (minus (arg1 a))
       <->  (union #{`(~'-> ~(L a) (~'<-> ~(L (arg1 a)) ~(L (arg2 a))))}
                   (plus (arg1 a))
                   (plus (arg2 a))
                   (minus (arg1 a))
                   (minus (arg2 a)))
       ->   (union #{`(~'-> ~(L a) (~'-> ~(L (arg1 a)) ~(L (arg2 a))))}
                   (minus (arg1 a))
                   (plus (arg2 a)))))))

(def minus
  ;; Must be memoized for complexity bounds to hold.
  (memoize
   (fn [a]
     (treecase a
       leaf #{}
       and  (union #{`(~'-> (~'and ~@(map L (args a))) ~(L a))}
                   (apply union (map minus (args a))))
       or   (if (clause? a)
              #{`(~'-> ~a ~(L a))}
              (union #{`(~'-> (~'or ~@(map L (args a))) ~(L a))}
                     (apply union (map minus (args a)))))
       not  (plus (arg1 a))
       <->  (union #{`(~'-> (~'<-> ~(L (arg1 a)) ~(L (arg2 a))) ~(L a))}
                   (minus (arg1 a))
                   (minus (arg2 a))
                   (plus (arg1 a))
                   (plus (arg2 a)))
       ->  (union #{`(~'-> (~'-> ~(L (arg1 a)) ~(L (arg2 a))) ~(L a))}
                  (plus (arg1 a))
                  (minus (arg2 a)))))))

(deftest plus-test
  (testing "http://dl.acm.org/citation.cfm?id=7244"
    (reset-counter!)
    (is (= (plus '(or (and q1 q2) (and q3 q4)))
           #{'(-> P0 (or P1 P2))
             '(-> P1 (and q1 q2))
             '(-> P2 (and q3 q4))}))
    (reset-counter!)
    (is (= (plus '(or (and q1 q2) (not (and q3 q4))))
           #{'(-> P0 (or P1 (not P2)))
             '(-> P1 (and q1 q2))
             '(-> (and q3 q4) P2)}))))

;;;_  * Proof search ---------------------------------------------------
;;;_   * Loop ----------------------------------------------------------
;; FIXME: assert no empty clauses?
(defn- search
  "Try to find a satisfying assignment for CNF formula A."
  ([a]
     (search a 100 1000 0.5 1))
  ([a max-cores]
     (search a 100 1000 0.5 max-cores))
  ([a max-tries max-flips p max-cores]
     (let [prms    (promise)
           futures (doall
                    (for [i (range max-cores)]
                      (do ;; (println "Starting thread" i)
                          (future
                            (let [res (do-search a max-tries max-flips p)]
                              (when res (deliver prms res)))))))]
       (loop []
         (let [res (deref prms 1000 :timeout)]
           (if (= res :timeout)
             (if (some #(not (future-done? %)) futures)
               (recur)
               nil)
             (do (doall (for [f futures] (future-cancel f)))
                 res)))))))

(defrecord Result [t])

(defn- do-search [a max-tries max-flips p]
  (let [a (prepare a)]
    (try+
     (let [i (atom 0)]
       (while (< @i max-tries)
         (let [a (atom (initialize a))
               j (atom 0)]
           (while (< @j max-flips)
             (if (satisfied? @a)
               (throw+ (Result. (assignment @a)))
               (do (swap! a #(wsat % p))
                   (swap! j inc))))
           (swap! i inc))))
     (catch Result res (:t res)))))

(deftest search-test
  (is (= {}                (search '())))
  (is (= {'a true 'b true} (search '([a] [b]))))
  (is (= nil               (search '([a] [(not a)])))))

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
  "Compute some useful indices."
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
    (is (= '([(not a) b] [a b c]) (clauses a 'a)))
    (is (= '(2 1 0)               (idxs a 'b)))
    (is (= '(b a)                 (vars a 1)))))


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
(defn- rand-bool [] (case (rand-int 2) 0 false 1 true))

(defn- fresh-assignment
  "A random truth assignment for VARS. Assignments are mappings from
   variable-symbols to booleans."
  [vars] (reduce (fn [acc var] (assoc acc var (rand-bool))) {} vars))

;; Derive a subset of entries from an index:
(defn- subindex [pred? index]
  (set (mapcat (fn [[k v]] (if (pred? k) (list v) nil)) index)))

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
  (if (empty? clause)
    false
    (or (eval-literal (first clause) t) (recur (rest clause) t))))

(defn- eval-literal [lit t] (if (symbol? lit) (t lit) (not (t (second lit)))))

(deftest eval-test
  (is (= false (eval-clause '(a)         {'a false})))
  (is (= true  (eval-clause '(a b)       {'a true 'b true})))
  (is (= true  (eval-clause '((not a) b) {'a true 'b true}))))

;;;_   * Step ----------------------------------------------------------
(defn- satisfied? [a] (nil? (seq (unsat-clauses a))))

(defn- wsat
  "Flip a single variable. First, pick a random unsatisfied clause.
   Then, either greedily or randomly pick a variable from that clause
   to flip."
  [a p]
  (let [idx (rand-nth (seq (unsat-clauses a)))]
    (if (< (rand) p)
      (flip-random a idx)
      (flip-greedy a idx))))

(defn- flip-random [a idx] (flip a (rand-nth (vars a idx))))

(defn- flip-greedy [a idx] (flip a (best (vars a idx) a)))


(defn- best [vars a] (second (first (sort-by first (map #(score % a) vars)))))

(defn- score
  "Assign a score to VAR based on the decrease in the total number of
   unsatisfied clauses caused by flipping it."
  [var a]
  (let [clauses (clauses a var)
        t       (assignment a)
        sat0    (satcount clauses t)
        sat1    (satcount clauses (do-flip t var))]
    [(- sat0 sat1) var]))

(defn- satcount [clauses t]
  (reduce (fn [acc c] (if (eval-clause c t) (inc acc) acc)) 0 clauses))

(deftest best-test
  (let [a (initialize (prepare '([a])))]
    (is (= 'a (best (vars a 0) a))))
  (let [a {:var->clauses {'a '([a b] [(not a) b] [a c])
                          'b '([a b] [(not a) b])
                          'c '([a c])}
           :t   {'a true     ;1
                 'b false    ;-1
                 'c false}}] ;0
    (is (= '([-1 b] [0 c] [1 a]) (sort-by first (map #(score % a) '(a b c)))))
    (is (= 'b (best '(a b c) a)))))


(defn- flip [a var]
  (let [clauses     (zip (idxs a var) (clauses a var))
        t           (do-flip (assignment a) var)
        old-sat     (sat-clauses a)
        old-unsat   (unsat-clauses a)
        [sat unsat] (satsplit clauses t)]
    (assoc a
      :t     t
      :sat   (union (difference old-sat unsat) sat)
      :unsat (union (difference old-unsat sat) unsat))))

(defn- do-flip [t var] (assoc t var (not (t var))))

(defn- satsplit [clauses t]
  (reduce (fn [[sat unsat] [i c]]
            (if (eval-clause c t)
              [(conj sat i) unsat]
              [sat (conj unsat i)]))
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
