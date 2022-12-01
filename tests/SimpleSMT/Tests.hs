-- | A module providing functions useful for testing a backend for SimpleSMT.
module SimpleSMT.Tests
  ( testBackend,
    Source(..),
    sources
  ) where

import SimpleSMT.Tests.Solver (testBackend)
import SimpleSMT.Tests.Sources (Source(..), sources)
