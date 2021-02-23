module HsProof
    ( proof
    , printResult
    ) where

import           Control.Monad.Except           ( runExceptT )
import           Control.Monad.Trans.State      ( evalState )
import           HsProof.Types

-- | do proofs with intro
proof :: Prop -> Proof a -> ProofResult a
proof pp pf = evalState (runExceptT pf) (PropRef [pp] [])

printResult :: Show a => ProofResult a -> IO ()
printResult = putStrLn . showResult
