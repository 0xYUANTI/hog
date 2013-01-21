# Hog
Hog is a simple (< 1000 LoC), probabilistic (incomplete), parallel
(embarassingly) SAT solver written in Clojure.

Hog uses Bram Cohen's Improved WALKSAT [1, 2] algorithm for proof search
and a Tseitin-style encoding [3, 4] for CNF conversion.

[1] Local Search Strategies for Satisfiability Testing
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.2207
[2] Improving Walksat
http://bramcohen.livejournal.com/31075.html
[3]
http://
[4]
http://

## Usage
Hog's main interface is the hog.core/solve function, which comes with
documentation.

Also included is a reduction from SUDOKU to SAT - this may serve
as an example.

## TODO
add problems from the various sat competitions to test suit
(guess that means a DIMACS parser as well)
add special support for crypto problems (attacking hash functions, &c.)
add davis-putnam as an alternative to wsat
add SMT support (maybe go for DPLL(T) right away?)
add more reductions (like sudoku)
add support for predicate logic?

## License
Copyright 2012 jakob@primat.es

Distributed under the new BSD license.
