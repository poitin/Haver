# Haver
Haskell Verification Tool as described in the paper "Distilling Programs for Verification"

The implementation can be built and executed using stack.

The execution is a REPL, with the prompt "POT> " and the following commands:

POT> :help

:load filename          To load the given filename  
:prog                   To print the current program  
:term                   To print the current term  
:eval                   To evaluate the current program  
:verify                 To verify the current program
:quit                   To quit  
:help                   To print this message  

The first thing to do is to load a program file:

POT> :load plusassoc

This will load the program plusassoc.pot (the.pot extension is assumed).

To see the contents of this program:

POT> :prog  
main = eqNat (plus x (plus y z)) (plus (plus x y) z);  
plus x y = case x of  
                          Zero -> y  
                        | Succ(x) -> Succ(plus x y);  
eqNat x y = case x of  
                              Zero -> case y of  
                                                     Zero -> True  
                                                   | Succ(y) -> False  
                           | Succ(x) -> case y of  
                                                           Zero -> False  
                                                         | Succ(y) -> eqNat x y  

To see the top-level term:

POT> :term  
eqNat (plus x (plus y z)) (plus (plus x y) z)  

To evaluate the current program:

POT> :eval

This will prompt for values of the free variables:

x = 1  
y = 2  
z = 3  
True   
Reductions: 74  
Allocations: 25  

To verify the current program:

POT> :verify  
True

To quit from the program:

POT> :quit