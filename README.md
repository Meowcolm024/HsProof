# HsProof

A simple theorem proofer written in Haskell.

current status:

``` haskell
-- | q -> (q -> ~q) -> (~p -> r /\ s) -> r
exampleTheorem :: Prop
exampleTheorem =
    Not (Atom "q")
        :-> (Atom "p" :-> Atom "q")
        :-> (Not (Atom "p") :-> (Atom "r" :/\ Atom "s"))
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
