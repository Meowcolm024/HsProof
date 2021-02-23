import           HsProof
import           HsProof.Logic
import           HsProof.Proof
import           HsProof.ProofRef
import           HsProof.Types

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

main :: IO ()
main = do
    putStrLn $ "Prove: " ++ show hw
    putStr "Result: "
    printResult proofhw
