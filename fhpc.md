% Preventing Data Races with Refinement Types
% George Stelle

One of the most pervasive and pernicious classes of bugs for the high
performance computing engineer is the data race, when two or more concurrent
threads access shared data without any mutual exclusion mechanism. Often these
bugs are hard to detect, hard to locate, and hard to debug. Most existing
programming models in HPC are of little help, providing almost no support for
preventing this class of errors. As any functional programmer should when faced
with a class of runtime error, we turn to the type system to prevent it.  While
there are a variety of possible approaches, we us LiquidHaskell, which allows us
to refine our types in an expressive way, while leaving the burden of proof to
the underlying SMT solver. Precisely, we show how we can statically prevent data
races, along with other well known errors, for low level, concurrent code. 


