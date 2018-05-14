# Type checker

## Syntax

### Types

- `Int`
- `?`
- `()`
- `A`
- `forall A . A`
- `Bool`

### Expressions

- unit `()`
- addition, `e1 + e2`
- lambdas `\ x -> e`
- annotated lambdas ` \ (x : A) -> e`
- applications `e1 e2`
- let expression `let x = e1 in e2`
- bool values, `true`, `false`

## Example

```haskell
-- fold
(\e -> e) : forall A . (forall B. B -> (A -> (forall C . C -> (A -> ? -> C) -> C) -> B) -> B) -> (forall B . B -> (A -> ? -> B) -> B) 

-- unfold
(\e -> e) : forall A . (forall  B . B -> (A -> ? -> B) -> B) -> (forall B . B -> (A -> (forall C . C -> (A -> ? -> C) -> C) -> B) -> B) 

-- nil
let fold = (\e -> e) : forall A . (forall B. B -> (A -> (forall C . C -> (A -> ? -> C) -> C) -> B) -> B) -> (forall B . B -> (A -> ? -> B) -> B) 
in 
let nil = (fold (\n -> \c -> n)) 
in 
nil

-- cons
let fold = (\e -> e) : forall A . (forall B. B -> (A -> (forall C . C -> (A -> ? -> C) -> C) -> B) -> B) -> (forall B . B -> (A -> ? -> B) -> B) 
in 
let nil = (fold (\n -> \c -> n)) 
in 
let cons = (\x -> \xs -> (\n -> \c -> c x xs)) : (forall A . A -> (forall B. B -> (A -> ? -> B) -> B) -> (forall B. B -> (A -> ? -> B) -> B)) 
in 
cons 1 ((cons 2 nil))

-- fix
(\f -> (\(x : ?) -> f (x x))(\(x : ?) -> f (x x))) : forall A . (A -> A) -> A 

-- Heterogeneous Containers.

let fold = (\e -> e) : forall A . (forall B. B -> (A -> (forall C . C -> (A -> ? -> C) -> C) -> B) -> B) -> (forall B . B -> (A -> ? -> B) -> B) 
in 
let nil = (fold (\n -> \c -> n)) 
in 
let cons = (\x -> \xs -> (\n -> \c -> c x xs)) : (forall A . A -> (forall B. B -> (A -> ? -> B) -> B) -> (forall B. B -> (A -> ? -> B) -> B)) 
in 
cons (true:?) ((cons (1:?) nil))
```
