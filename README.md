# Homework 2 CS350A
## Contributors
- K. Siddarth 150312
- Saket Jhunjhunwala 150619

We have attempted all questions. 

## Directions
To run the code, please use the Mozart interpreter in emacs (using ozc does not work). The state of the environment and store are outputted in the emulator buffer. We use `Show` to print the environment and SAS.

Assign the variable `Prog` with the AST (in line 10). Now run the file.

## Description

 Environment is printed as a nested list with first element representing the identifier and second element representing the corresponding SAS variable. SAS variables are represented by Natural numbers. The values in SAS are records represented as `value(w)` where `w` is any value or `t` for true and `f` for false. Procedure values are represented as tuples with first being the procedure definition and second value being the list of free variables and the corresponding SAS variables.

 ### Note: Since `proc` is a keyword in Oz, we use `proc1`

 The state of the SAS and environment are printed after instruction is executed, i.e., after the statemeent is popped from the semantic stack. 

 For `add` and `product`, we add two statements to the operational semantics.

- Add is done by `[add ident(x) ident(y) ident(z)]`. This denotes the statement `Z = X+Y`. 
- Product is done by `[mul ident(x) ident(y) ident(z)]`. This denotes the statement `Z = X*Y`. 

The code for Q9 in AST is given at line number `326`