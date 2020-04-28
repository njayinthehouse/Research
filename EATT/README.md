EA-TT
=====

EA-TT is a simple type theory based on Elementary Affine Logic, which can be
seen as a linear language extended with a controlled duplication discipline.
This greatly amplifies its power, allowing it to perform loops and bounded
recursion, and gives it 2 key benefits:

1. It can be evaluated optimally on interaction nets without bookkeeping.

2. It has a straightforward termination proof that doesn't rely on types.

Because of #2, we're able to allow non-termination on the type level without
breaking consistency. That means convenient features such as `Type : Type`,
type-level recursion and self-types can be exploited, which, in turn, allow us
to derive induction. The main drawback of EA-TT is that, by having a very rigit
duplication discipline, we can't implement recursive algorithms directly, and
must instead emulate them with bounds, which can be annoying. Regardless, EA-TT
is simple, elegant and computationally powerful proof language featuring
inductive reasoning.

This document is a quick draft made following a request on
https://t.me/formality_lang.


Syntax
------

EA-TT terms are defined by the following syntax:

```haskell
name ::=
  (alphanumeric)

defs ::=
  | name : term = term; defs -- top-level definition
  | <eof>                    -- end of file

term ::=
  (name: term) -> term  -- function type
  λname.term            -- function intr
  (term term)           -- function elim                
  ! term                -- box type
  # term                -- box intr
  dup var = term; term  -- box elim
  ${name} term          -- self type
  $intr{x : term} term  -- self intr
  $elim{term}           -- self elim
  Type                  -- type
  name                  -- variable
  name                  -- reference
```

Evaluation
----------

```
(λx.body argm)
---------------- application
body[x <- argm]

dup x = #expr; body
------------------- duplication
body[x <- expr]

(dup x = a; b)(c)
----------------- app-dup permutation
dup x = a; b(c)

dup x = (dup y = a; b); c
------------------------- dup-dup permutation
dup y = a; dup x = b; c
```

Example:

```
dup a = #λx.x; dup b = #λy.(y a); #(b b)
dup b = #(λy.y λx.x); #(b b) -- duplication
dup b = #λx.x; #(b b)        -- application
# (λx.x λx.x)                -- duplication
# λx.x                       -- application
```

Typing
------

```
ctx |- A : Type    ctx, x : A |- B : Type
----------------------------------------- function type
ctx |- ((x: A) -> B) : Type

ctx, x : A |- f : B
------------------- function intr
ctx |- λx.f : (x : A) -> B

ctx |- f : (x : A) -> B    ctx |- a : A
--------------------------------------- function elim
ctx |- (f a) : B[x <- a]

ctx |- A : Type
---------------- box type
ctx |- !A : Type

ctx |- a : A
-------------- box intr
ctx |- #a : !A 

ctx |- a : !A    ctx, x : A |- b : B
------------------------------------ box elim
(dup x = a; b) : B

ctx, x : ${x}A |- A : Type
-------------------------- self type
ctx |- ${x}A : Type

ctx |- t : A[x <- t]
-------------------------- self intr
ctx |- $intr{x:A}t : ${x}A

ctx |- t : ${x}A
--------------------------- self elim
ctx |- $elim{t} : A[x <- t]

x : A in defs
------------- definition
x : A
```

Stratification
--------------

Let `uses(x,f)` count the number of occurrences of `x` in `f`, and `level(x,f)`
count the number of boxes surrounding `x` in `f`, if it is unique. Example:

```
uses(x, a)        == 0    -- x isn't used
uses(x, (f x))    == 1    -- x is used once
uses(x, (x x))    == 2    -- x is used twice
level(x, a)       == ∅    -- x doesn't appear
level(x, (f x))   == 0    -- x has 0 surrounding boxes
level(x, (f #x))  == 1    -- x has 1 surrounding boxes
level(x, #(f x))  == 1    -- x has 1 surrounding boxes
level(x, (#f #x)) == 1    -- x has 1 surrounding boxes
level(x, (f ##x)) == 2    -- x has 2 surrounding boxes
level(x, #(f #x)) == 2    -- x has 2 surrounding boxes
level(x, ##(f x)) == 2    -- x has 2 surrounding boxes
level(x, #(x #x)) == ∅    -- x has 1 and 2 surrounding boxes (forbidden)
```

Then a term is stratified when:

```
ctx |- A : Type
---------------
stratified(A)

stratified(f)    uses(x,f) <= 1    level(x,b) == 0
--------------------------------------------------
stratified(λx.f) 

stratified(a)    stratified(b)    level(x,f) == 1
-------------------------------------------------
dup x = a; b

stratified(f)   stratified(a)
-----------------------------
stratified((f a))

stratified(t)
------
stratified(#t)
```

In other words:

- Types are stratified.

- A lambda is stratified when its body is, and its variable is only
  used at most once at level 0.

- A duplication is stratified when its expression is, its body is, and
  its variable is only used at level 1.

- An application is stratified when its function and arguments are.

- A box is stratified when its expression is.

Note this enforces important structural properties. For example, boxed terms
can't have free variables. For example, `#f` can't have a variable bound by an
outside lambda. That's because such occurrence would be at a level higher than
the lambda itself, which is forbidden. Moreover, there is always one box between
the binding of a dup variable and its occurrence. For example,
`dup x = a; #(f x)` and `dup x = a; (f #x)` are stratified, but
`dup x = a; (f x)` and `dup x = a; ##(f x)` are not.

Termination
===========

Let `profile(t, n)` be the number of applications and duplications at level `n`
of a term `t`. For example, the following term:

```
λt. ((t #λx.x) #(λy.y λz.z))
```

Has the following profile:

```
profile(t, 0) == 2
profile(t, 1) == 1
```

Because there are 2 applications on level 0 and 1 application on level 1.

The following term:

```
λf.
  dup a = (λk.k #f)
  dup b = #λx. (a (a x))
  # λx. (b (b x))
```

Has the following profile:

```
profile(t, 0) == 3
profile(t, 1) == 4
```

Because there are 1 application and 2 duplications on level 0 and 4 applications
on level 1.

The key fact to note is that evaluating a redex on level `n` of a term `t`
always decreases `profile(t, n)` by at least 1, and leaves `profile(t, m)`
untouched for any `m < n`. Let's consider the relevant reductions.

An application on level `n`:

```
(λx. f)(a)
```

Evaluates to `f[x <- a]`. Since `x` can only occur at most once (because lambdas
are affine), then no new applications or duplications can be created by that
evaluation. Moreover, since the number of boxes surrounding 

Since the number of boxes surrounding the occurrence of `x` in `f` must be `0`,
then `a` will stay on level `n` after reduction.  Moreover, since `x` only
occurs at most once, then no new applications or duplications can be created on
that level. Since evaluating an application consumes it, then `profile(t, n)`
decreases by at least 1, and `profile(t, m)` remains unchanged for any `m < n`.

A duplication on level `n`:

```
dup x = #a; b
```

Evaluates to `b[x <- a]`.

Since `x` can occur several times, this operation can create new application and
duplications, but only in levels higher than `n`. Since the number of boxes
surrounding the occurrence of `x` in `b` must be `1`, then `a` will stay on
level `n + 1`. As such, evaluating a duplication decreases `profile(t, n)`
decreases by at least 1, and leaves `profile(t, m)` unchanged for any `m < n`.

Since evaluating a regex on level `n` reduces `profile(t, n)` by at least 1,
then we can normalize a term by evaluating all redexes on level `0`, then all
redexes on level `1` and so on, until no more redexes are left in any level.

Type Preservation
=================

Evaluating a term doesn't change its type. Proof should be straightforward since
the typing rules are mostly standard.

Consistency
===========

We can't construct a term of type `(A : Type) -> A`. This easily follows from
type preservation and termination.

Induction
=========

The induction principle on Nats can be derived as follows:

```
Nat : Type
  ${self}
  (P : (n : Nat) -> Type) ->
  (s : ! (n : Nat) -> (h : (P n)) -> (P (succ n))) ->
  (z : ! (P zero)) ->
  ! (P self)

succ : (n : Nat) -> Nat
  λn.
  $intr{Nat} λP. λs. λz.
  dup succ = s;
  dup zero = z;
  dup pred = ((($elim{n} P) #succ) #zero);
  # ((succ n) pred)

zero : Nat
  $intr{Nat} λP. λs. λz.
  dup succ = s;
  dup zero = z;
  # zero

induction
  : (P : (:Nat) -> Type) ->
    (s : ! (n : Nat) -> (x : (P n)) -> (P (succ n))) ->
    (z : ! (P zero)) ->
    (n : Nat) ->
    ! (P n)
  λP. λs. λz. λn.
  dup succ = s;
  dup zero = z;
  (((n P) #succ) #zero)
```

Scott-Encoded datatypes can be used to emulate Haskell and Agda-like datatypes,
while Church-Encoded datatypes like the one above can be used to emulate loops
and bounded recursion.

More info
---------

This, again, is a rushed draft I made on request. Sadly, we don't have all that
info in a more organized and presentable format right now, and it is not our
near-term priority. Once we have Formality in a more mature state, we will be
delighted to formalize all that stuff in our own language. For now, I hope this
is enough info to at least give an idea of what EA-TT is about. I also wrote
some things about it in an (also outdated) post
[here](https://medium.com/@maiavictor/introduction-to-formality-part-1-7ae5b02422ec).
