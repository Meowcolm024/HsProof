# HsProof

![workflow](https://github.com/meowcolm024/HsProof/actions/workflows/haskell.yml/badge.svg)

A simple proof assistant written in *Haskell*.

This is an extremely poorly-designed proof assistant that is not meant for practical use.
But it is a really fun project to work with :P

I simply use this project to spractice using *monad transformers*, *state monad* and *lenses* :D

## Build

build:

``` sh
$ stack build
```

run the example:

``` sh
$ stack exec HsProof-example
Prove: (~t -> ((s -> t) -> (((~r \/ ~f) -> (s /\ l)) -> r)))
Result: Q.E.D.
```

## Examples

A simple example:

``` haskell
-- predicates: 
--     (1) q 
--     (2) p -> q 
--     (3) ~p -> r /\ s
-- to proof: r
exampleTheorem :: Prop
exampleTheorem =
    Not (Atom "q")
        :-> (Atom "p" :-> Atom "q")
        :-> (Not (Atom "p") :-> Atom "r" :/\ Atom "s")
        :-> Atom "r"

proofExample :: ProofResult PropRef
proofExample = proof exampleTheorem $ do
    a <- intro      -- ~q
    h <- intro      -- p -> q
    g <- intro      -- ~p -> (r /\ s)
    contrapostive `applyTo'` h
    (h >$> g) >>= (`applyTo'` a)
    disjunctionL `applyTo'` a
    apply a
    qed
```

Here is another [example](example/Example.hs):

``` haskell
-- | ~t -> (s -> t) -> (~r \/ ~f -> s /\ l) -> r
hw :: Prop
hw =
    Not (Atom "t")
        :-> (Atom "s" :-> Atom "t")
        :-> (Not (Atom "r") :\/ Not (Atom "f") :-> Atom "s" :/\ Atom "l")
        :-> Atom "r"

proofhw :: ProofResult PropRef
proofhw = proof hw $ do
    p  <- intro                         -- p: ~t
    h1 <- intro                         -- h1: s -> t
    h2 <- intro                         -- h2: ~r \/ ~f -> s /\ l
    contrapostive `applyTo'` h1         -- h1: ~t -> ~s
    q <- applyToM imply [h1, p]         -- q: ~s
    contrapostive `applyTo'` h2         -- h2: ~(s /\ l) -> ~(~r \/ ~f)
    -- create a tmp l for addition: ~s -> ~s \/ ~l
    tmp <- newProofObject (Not (Atom "l"))
    t   <- applyToM addition [q, tmp]   -- t: ~s \/ ~l
    deMorgan `applyTo'` t               -- t: ~(s /\ l)
    applyToM' imply [h2, t] t           -- t: ~(~r \/ ~f)
    simpl `applyTo'` t                  -- t: r /\ f
    simplificationL `applyTo'` t        -- t: r
    apply t
    qed
```
