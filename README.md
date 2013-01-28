# Hog
Hog is a simple (< 1000 LoC), probabilistic (incomplete), parallel
(embarassingly) SAT solver written in Clojure.

Hog uses Bram Cohen's WALKSAT [1, 2] algorithm for proof search and a
Tseitin-style encoding [3, 4] for CNF conversion.

[1] Local Search Strategies for Satisfiability Testing  
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.2207  
[2] Improving Walksat  
http://bramcohen.livejournal.com/31075.html  
[3] On the Complexity of Derivation in Propositional Calculus  
http://www.decision-procedures.org/handouts/Tseitin70.pdf  
[4] A Structure-preserving Clause Form Translation  
http://dl.acm.org/citation.cfm?id=7244  

## Usage
Hog's main interface is the hog.core/solve function, which comes with
documentation.

Also included is a reduction from SUDOKU to SAT - this may serve
as an example.

## TODO
+ add problem sets from the various SAT competitions to test suit
+ add a DIMACS parser
+ add special support for crypto problems (attacking hash functions, &c.)
+ add Davis-Putnam as an alternative to WSAT
+ add SMT support (maybe go for DPLL(T) right away?)
+ add more reductions (like SUDOKU)
+ add support for predicate logic? QBF?

## License
Copyright 2012 jakob@primat.es

Distributed under the new BSD license.
