module Paths_data_category (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [0,0,3], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/sjoerd/.cabal/bin"
libdir     = "/Users/sjoerd/.cabal/lib/data-category-0.0.3/ghc-6.10.4"
datadir    = "/Users/sjoerd/.cabal/share/data-category-0.0.3"
libexecdir = "/Users/sjoerd/.cabal/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "data_category_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "data_category_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "data_category_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "data_category_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
