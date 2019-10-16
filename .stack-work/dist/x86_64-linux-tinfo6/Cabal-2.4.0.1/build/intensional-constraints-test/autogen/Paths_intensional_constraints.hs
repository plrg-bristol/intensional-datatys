{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_intensional_constraints (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/bin"
libdir     = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/lib/x86_64-linux-ghc-8.6.5/intensional-constraints-0.1.0.0-GHWjVtGXjIO5fuOnpeqIXF-intensional-constraints-test"
dynlibdir  = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/lib/x86_64-linux-ghc-8.6.5"
datadir    = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/share/x86_64-linux-ghc-8.6.5/intensional-constraints-0.1.0.0"
libexecdir = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/libexec/x86_64-linux-ghc-8.6.5/intensional-constraints-0.1.0.0"
sysconfdir = "/home/eddie/Documents/GHC plugin/.stack-work/install/x86_64-linux-tinfo6/2a9efc81d20be8a99a756d7cb7103bb3410e46e6776c3c1927ae1f4d297d58cf/8.6.5/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "intensional_constraints_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "intensional_constraints_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "intensional_constraints_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "intensional_constraints_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "intensional_constraints_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "intensional_constraints_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
