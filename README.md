# HsProof

A simple theorem proofer written in Haskell.

current status:

``` haskell
-- | q -> (q -> ~q) -> (~p -> r /\ s) -> r
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

another example:

``` haskell
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
    h2 <- intro                         -- ~r \/ ~f -> s /\ l
    contrapostive `applyTo'` h1         -- ~t -> ~s
    q <- applyToM imply [h1, p]         -- q: ~ s
    contrapostive `applyTo'` h2         -- ~(s /\ l) -> ~ (~r \/ ~f)
    -- create a tmp l for addition: s -> s \/ l
    tmp <- newProofObject (Not (Atom "l"))
    t   <- applyToM addition [q, tmp]   -- t: ~s \/ ~l
    deMorgan `applyTo'` t               -- ~ (s /\ l)
    applyToM' imply [h2, t] t           -- ~(~r \/ ~f)
    deMorgan `applyTo'` t               -- ~~r /\ ~~f
    eliminateDN `applyTo'` t            -- r /\ f
    simplificationL `applyTo'` t        -- r
    apply t
    qed
```
