;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Reduce instances of SUDOKU to instances of SAT.
;;;
;;; ``The objective is to fill a 9x9 grid with digits so that each column,
;;; each row, and each of the nine 3x3 sub-grids that compose the grid
;;; (also called "boxes", "blocks", "regions", or "sub-squares") contains
;;; all of the digits from 1 to 9. The puzzle setter provides a partially
;;; completed grid, which typically has a unique solution.''
;;; ~ http://en.wikipedia.org/wiki/Sudoku
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_* Declarations =====================================================
(ns hog.sudoku
  (:use [clojure.math.numeric-tower :only [sqrt]]
        [clojure.math.combinatorics :only [cartesian-product]]
        [clojure.test]))

(declare encode decode)
(declare indexed get-rows get-cols get-boxs)
(declare puzzle-constraints row-constraints col-constraints box-constraints)
(declare mkvar pairs uniqueness-constraints)

;;;_* Code =============================================================
;;;_ * API -------------------------------------------------------------
(defn sudoku
  "Solve an instance of SUDOKU via reduction to SAT.
   SUDOKU instances are represented as seqs with NxN elements (the
   elements of the first to Nth rows from left to right).
   Each element is either nil (blank) or an integer between 1 and 9."
  [puzzle]
  (decode
   (#'hog.core/search (#'hog.core/Cl (encode puzzle))
                      100
                      20000
                      0.5
                      1))
  ;; (-> puzzle
  ;;     encode
  ;;     hog.core/solve
  ;;     decode)
  )

;;;_ * Encode ----------------------------------------------------------
(defn- encode
  "To translate a Sudoku problem into a SAT problem, I make one boolean
   variable for each possible state of each cell of the original
   problem, so there's one variable for whether the upper-left cell is a
   one, another for whether it's a two, etc. Translating the constraints
   on the Sudoku problem is then straightforward - each digit must occur
   exactly once in each row, column, and subsquare, and each pair of
   cells in each row, column, or subsquare must not both be true
   (expressed as, either the first one is false or the second one is
   false)."
  [puzzle]
  (let [puzzle (indexed puzzle)
        rows   (get-rows puzzle)
        cols   (get-cols rows)
        boxs   (get-boxs rows)]
    `(~'and ~@(puzzle-constraints puzzle)
            ~@(row-constraints rows)
            ~@(col-constraints cols)
            ~@(box-constraints boxs))))

;;;_  * Views ----------------------------------------------------------
(defn- indexed [xs] (map #(vector %1 %2) (range (count xs)) xs))

(deftest indexed-test
  (is (= '([0 a] [1 b] [2 c]) (indexed '(a b c)))))


(defn- get-rows [puzzle]
  (partition (sqrt (count puzzle)) puzzle))

(deftest get-rows-test
  (is (= '((1 2 3)
           (4 5 6)
           (7 8 9))
         (get-rows '(1 2 3 4 5 6 7 8 9)))))

(defn- get-cols [rows]
  (reverse
   (reduce (fn [acc n] (cons (map #(nth % n) rows) acc))
           ()
           (range (count rows)))))

(deftest get-cols-test
  (is (= '((1 4 7)
           (2 5 8)
           (3 6 9))
         (get-cols (get-rows '(1 2 3 4 5 6 7 8 9))))))

(defn- get-boxs [rows]
  (let [dims    (sqrt (count (first rows)))
        coords  (cartesian-product (range dims) (range dims))
        get-box (fn [i j]
                  (mapcat #(take dims (drop (* i dims) %))
                       (take dims (drop (* j dims) rows))))]
    (reverse
     (reduce (fn [acc [i j]] (cons (get-box i j) acc))
             '()
             coords))))

(deftest get-boxs-test
  (is (= '((1 2 5 6)
           (9 10 13 14)
           (3 4 7 8)
           (11 12 15 16))
         (get-boxs '((1   2  3  4)
                     (5   6  7  8)
                     (9  10 11 12)
                     (13 14 15 16)))))
  (is (= '((1 2 3 10 11 12 19 20 21)
           (28 29 30 37 38 39 46 47 48)
           (55 56 57 64 65 66 73 74 75)
           (4 5 6 13 14 15 22 23 24)
           (31 32 33 40 41 42 49 50 51)
           (58 59 60 67 68 69 76 77 78)
           (7 8 9 16 17 18 25 26 27)
           (34 35 36 43 44 45 52 53 54)
           (61 62 63 70 71 72 79 80 81))
         (get-boxs (get-rows
                    '(1   2  3  4  5  6  7  8  9
                      10 11 12 13 14 15 16 17 18
                      19 20 21 22 23 24 25 26 27
                      28 29 30 31 32 33 34 35 36
                      37 38 39 40 41 42 43 44 45
                      46 47 48 49 50 51 52 53 54
                      55 56 57 58 59 60 61 62 63
                      64 65 66 67 68 69 70 71 72
                      73 74 75 76 77 78 79 80 81))))))

;;;_  * Constraints ----------------------------------------------------
(defn- puzzle-constraints
  ([puzzle]
     (puzzle-constraints puzzle (range 1 10)))
  ([puzzle vals]
     (mapcat (fn [[idx val]]
               (if val
                 (list (mkvar idx val))
                 (let [vars  (map #(mkvar idx %) vals)
                       vps   (pairs vars)]
                   `((~'or ~@vars)
                     ~@(map (fn [[v1 v2]] `(~'or (~'not ~v1) (~'not ~v2)))
                            vps)))))
             puzzle)))

(defn- pairs [xs]
  (if-let [v1 (first xs)]
    (concat (map (fn [v2] [v1 v2]) (rest xs))
            (pairs (rest xs)))
    ()))

(deftest puzzle-constraints-test
  (is (= '(cell_0=2
           (or cell_1=1 cell_1=2 cell_1=3)
           (or (not cell_1=1) (not cell_1=2))
           (or (not cell_1=1) (not cell_1=3))
           (or (not cell_1=2) (not cell_1=3)))
         (puzzle-constraints (indexed '(2 nil)) '(1 2 3)))))


(defn- row-constraints [rows] (uniqueness-constraints rows))
(defn- col-constraints [cols] (uniqueness-constraints cols))
(defn- box-constraints [boxs] (uniqueness-constraints boxs))

(defn- uniqueness-constraints
  ([cell-lists]
     (uniqueness-constraints cell-lists (range 1 10)))
  ([cell-lists vals]
     (mapcat (fn [cells]
               (mapcat (fn [val]
                         (let [vars (map (fn [[idx _]] (mkvar idx val))
                                         cells)
                               vps (pairs vars)]
                           `((~'or ~@vars)
                             ~@(map (fn [[v1 v2]] `(~'or (~'not ~v1) (~'not ~v2)))
                                    vps))))
                    vals))
             cell-lists)))

(deftest uniqueness-constraints-test
  (is (= '((or cell_0=1 cell_1=1 cell_2=1)
           (or (not cell_0=1) (not cell_1=1))
           (or (not cell_0=1) (not cell_2=1))
           (or (not cell_1=1) (not cell_2=1))

           (or cell_0=2 cell_1=2 cell_2=2)
           (or (not cell_0=2) (not cell_1=2))
           (or (not cell_0=2) (not cell_2=2))
           (or (not cell_1=2) (not cell_2=2))

           (or cell_0=3 cell_1=3 cell_2=3)
           (or (not cell_0=3) (not cell_1=3))
           (or (not cell_0=3) (not cell_2=3))
           (or (not cell_1=3) (not cell_2=3)))
       (uniqueness-constraints '(([0 nil] [1 nil] [2 nil])) '(1 2 3)))))


(defn- mkvar [idx val] (symbol (str "cell_" idx "=" val)))

;;;_ * Decode ----------------------------------------------------------
(defn- parse [sym]
  (let [s (str sym)]
    (Integer/parseInt (subs s (inc (.indexOf s "="))))))

(defn- decode
  "Pretty-print a SUDOKU assignment."
  [solution]
  (map parse
       (mapcat (fn [idx]
                 (filter #(and (contains? solution %) (solution %))
                         (map #(mkvar idx %)
                              (range 1 10))))
               (range 81))))

;;;_* Tests ============================================================
(deftest sudoku-test
  (testing "http://en.wikipedia.org/wiki/Sudoku"
    (is (= '(5 3 4 6 7 8 9 1 2
             6 7 2 1 9 5 3 4 8
             1 9 8 3 4 2 5 6 7
             8 5 9 7 6 1 4 2 3
             4 2 6 8 5 3 7 9 1
             7 1 3 9 2 4 8 5 6
             9 6 1 5 3 7 2 8 4
             2 8 7 4 1 9 6 3 5
             3 4 5 2 8 6 1 7 9)
         (sudoku '(5 3 nil nil 7 nil nil nil nil
                   6 nil nil 1 9 5 nil nil nil
                   nil 9 8 nil nil nil nil 6 nil
                   8 nil nil nil 6 nil nil nil 3
                   4 nil nil 8 nil 3 nil nil 1
                   7 nil nil nil 2 nil nil nil 6
                   nil 6 nil nil nil nil 2 8 nil
                   nil nil nil 4 1 9 nil nil 5
                   nil nil nil nil 8 nil nil 7 9)))))
  (testing "http://bramcohen.livejournal.com/70250.html"
    (is (coll?
         (sudoku '(nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil
                   nil nil nil nil nil nil nil nil nil))))))

;;;_* Emacs ============================================================
;;; Local Variables:
;;; allout-layout: t
;;; End:
