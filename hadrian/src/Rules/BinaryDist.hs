module Rules.BinaryDist where

import Hadrian.Haskell.Cabal

import CommandLine
import Context
import Expression
import Oracles.Setting
import Oracles.Flag
import Packages
import Settings
import Settings.Program (programContext)
import Target
import Utilities
import qualified System.Directory.Extra as IO

{-
Note [Binary distributions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Hadrian produces binary distributions under:
  <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>.tar.xz

It is generated by creating an archive from:
  <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/

It does so by following the steps below.

- make sure we have a complete stage 2 compiler + haddock

- copy the bin and lib directories of the compiler we built:
    <build root>/stage1/{bin, lib}
  to
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/{bin, lib}

- copy the generated docs (user guide, haddocks, etc):
    <build root>/docs/
  to
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/docs/

- copy haddock (built by our stage2 compiler):
    <build root>/stage2/bin/haddock
  to
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/bin/haddock

- use autoreconf to generate a `configure` script from
  aclocal.m4 and distrib/configure.ac, that we move to:
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/configure

- write a (fixed) Makefile capable of supporting 'make install' to:
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/Makefile

- write some (fixed) supporting bash code for the wrapper scripts to:
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/wrappers/<program>

  where <program> is the name of the executable that the bash file will
  help wrapping.

- copy supporting configure/make related files
  (see @bindistInstallFiles@) to:
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/<file>

- create a .tar.xz archive of the directory:
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>/
  at
    <build root>/bindist/ghc-<X>.<Y>.<Z>-<arch>-<os>.tar.xz


Note [Wrapper scripts and binary distributions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Users of Linux, FreeBSD, Windows and OS X can unpack a
binary distribution produced by hadrian for their arch
and OS and start using @bin/ghc@, @bin/ghc-pkg@ and so on
right away, without even having to configure or install
the distribution. They would then be using the real executables
directly, not through wrapper scripts.

This works because GHCs produced by hadrian on those systems
are relocatable. This means that you can copy the @bin@ and @lib@
dirs anywhere and GHC will keep working, as long as both
directories sit next to each other. (This is achieved by having
GHC look up its $libdir relatively to where the GHC executable
resides.)

It is however still possible (and simple) to install a GHC
distribution that uses wrapper scripts. From the unpacked archive,
you can simply do:

  ./configure --prefix=<path> [... other configure options ...]
  make install

In order to support @bin@ and @lib@ directories that don't sit next to each
other, the install script:
   * installs programs into @LIBDIR/ghc-VERSION/bin@
   * installs libraries into @LIBDIR/ghc-VERSION/lib@
   * installs the wrappers scripts into @BINDIR@ directory

-}

bindistRules :: Rules ()
bindistRules = do
    root <- buildRootRules
    phony "install" $ do
        need ["binary-dist-dir"]
        version        <- setting ProjectVersion
        targetPlatform <- setting TargetPlatformFull
        let ghcVersionPretty = "ghc-" ++ version ++ "-" ++ targetPlatform
            bindistFilesDir  = root -/- "bindist" -/- ghcVersionPretty
            prefixErr = "You must specify a path with --prefix when using the"
                     ++ " 'install' rule"
        installPrefix <- fromMaybe (error prefixErr) <$> cmdPrefix
        runBuilder (Configure bindistFilesDir) ["--prefix="++installPrefix] [] []
        runBuilder (Make bindistFilesDir) ["install"] [] []

    phony "binary-dist-dir" $ do
        -- We 'need' all binaries and libraries
        targets <- mapM pkgTarget =<< stagePackages Stage1
        cross <- flag CrossCompiling
        need targets
        unless cross $ needIservBins

        version        <- setting ProjectVersion
        targetPlatform <- setting TargetPlatformFull
        distDir        <- Context.distDir Stage1
        rtsDir         <- pkgIdentifier rts

        let ghcBuildDir      = root -/- stageString Stage1
            bindistFilesDir  = root -/- "bindist" -/- ghcVersionPretty
            ghcVersionPretty = "ghc-" ++ version ++ "-" ++ targetPlatform
            rtsIncludeDir    = ghcBuildDir -/- "lib" -/- distDir -/- rtsDir
                               -/- "include"

        -- We create the bindist directory at <root>/bindist/ghc-X.Y.Z-platform/
        -- and populate it with Stage2 build results
        createDirectory bindistFilesDir
        copyDirectory (ghcBuildDir -/- "bin") bindistFilesDir
        copyDirectory (ghcBuildDir -/- "lib") bindistFilesDir
        copyDirectory (rtsIncludeDir)         bindistFilesDir

        unless cross $ need ["docs"]

        -- TODO: we should only embed the docs that have been generated
        -- depending on the current settings (flavours' "ghcDocs" field and
        -- "--docs=.." command-line flag)
        -- Currently we embed the "docs" directory if it exists but it may
        -- contain outdated or even invalid data.

        -- Use the IO version of doesDirectoryExist because the Shake Action
        -- version should not be used for directories the build system can
        -- create. Using the Action version caused documentation to not be
        -- included in the bindist in the past (part of the problem in #18669).
        whenM (liftIO (IO.doesDirectoryExist (root -/- "docs"))) $ do
          copyDirectory (root -/- "docs") bindistFilesDir
        when windowsHost $ do
          copyDirectory (root -/- "mingw") bindistFilesDir
          -- we use that opportunity to delete the .stamp file that we use
          -- as a proxy for the whole mingw toolchain, there's no point in
          -- shipping it
          removeFile (bindistFilesDir -/- mingwStamp)

        -- We copy the binary (<build root>/stage1/bin/haddock[.exe]) to
        -- the bindist's bindir (<build root>/bindist/ghc-.../bin/).
        unless cross $ do
          haddockPath <- programPath (vanillaContext Stage1 haddock)
          copyFile haddockPath
                   (bindistFilesDir -/- "bin" -/- takeFileName haddockPath)

        -- We then 'need' all the files necessary to configure and install
        -- (as in, './configure [...] && make install') this build on some
        -- other machine.
        need $ map (bindistFilesDir -/-)
                   (["configure", "Makefile"] ++ bindistInstallFiles)
        need $ map ((bindistFilesDir -/- "wrappers") -/-)
                   [ "check-ppr", "check-exact", "ghc", "ghc-iserv", "ghc-pkg"
                   , "ghci-script", "haddock", "hpc", "hp2ps", "hsc2hs"
                   , "runghc"]


    let buildBinDist :: Compressor -> Action ()
        buildBinDist compressor = do
            need ["binary-dist-dir"]

            version        <- setting ProjectVersion
            targetPlatform <- setting TargetPlatformFull

            let ghcVersionPretty = "ghc-" ++ version ++ "-" ++ targetPlatform

            -- Finally, we create the archive <root>/bindist/ghc-X.Y.Z-platform.tar.xz
            tarPath <- builderPath (Tar Create)
            cmd [Cwd $ root -/- "bindist"] tarPath
                [ "-c", compressorTarFlag compressor, "-f"
                , ghcVersionPretty <.> "tar" <.> compressorExtension compressor
                , ghcVersionPretty ]

    phony "binary-dist" $ buildBinDist Xz
    phony "binary-dist-gzip" $ buildBinDist Gzip
    phony "binary-dist-bzip2" $ buildBinDist Bzip2
    phony "binary-dist-xz" $ buildBinDist Xz

    -- Prepare binary distribution configure script
    -- (generated under <ghc root>/distrib/configure by 'autoreconf')
    root -/- "bindist" -/- "ghc-*" -/- "configure" %> \configurePath -> do
        ghcRoot <- topDirectory
        copyFile (ghcRoot -/- "aclocal.m4") (ghcRoot -/- "distrib" -/- "aclocal.m4")
        copyDirectory (ghcRoot -/- "m4") (ghcRoot -/- "distrib")
        buildWithCmdOptions [] $
            target (vanillaContext Stage1 ghc) (Autoreconf $ ghcRoot -/- "distrib") [] []
        -- We clean after ourselves, moving the configure script we generated in
        -- our bindist dir
        removeFile (ghcRoot -/- "distrib" -/- "aclocal.m4")
        removeDirectory (ghcRoot -/- "distrib" -/- "m4")

        moveFile (ghcRoot -/- "distrib" -/- "configure") configurePath

    -- Generate the Makefile that enables the "make install" part
    root -/- "bindist" -/- "ghc-*" -/- "Makefile" %> \makefilePath -> do
        top <- topDirectory
        copyFile (top -/- "hadrian" -/- "bindist" -/- "Makefile") makefilePath

    root -/- "bindist" -/- "ghc-*" -/- "wrappers/*" %> \wrapperPath ->
        writeFile' wrapperPath $ wrapper (takeFileName wrapperPath)

    -- Copy various configure-related files needed for a working
    -- './configure [...] && make install' workflow
    -- (see the list of files needed in the 'binary-dist' rule above, before
    -- creating the archive).
    forM_ bindistInstallFiles $ \file ->
        root -/- "bindist" -/- "ghc-*" -/- file %> \dest -> do
            ghcRoot <- topDirectory
            copyFile (ghcRoot -/- fixup file) dest

  where
    fixup f | f `elem` ["INSTALL", "README"] = "distrib" -/- f
            | otherwise                      = f

data Compressor = Gzip | Bzip2 | Xz
                deriving (Eq, Ord, Show)

-- | Flag to pass to tar to use the given 'Compressor'.
compressorTarFlag :: Compressor -> String
compressorTarFlag Gzip  = "--gzip"
compressorTarFlag Xz    = "--xz"
compressorTarFlag Bzip2 = "--bzip"

-- | File extension to use for archives compressed with the given 'Compressor'.
compressorExtension :: Compressor -> String
compressorExtension Gzip  = "gz"
compressorExtension Xz    = "xz"
compressorExtension Bzip2 = "bz2"

-- | A list of files that allow us to support a simple
-- @./configure [...] && make install@ workflow.
bindistInstallFiles :: [FilePath]
bindistInstallFiles =
    [ "config.sub", "config.guess", "install-sh", "mk" -/- "config.mk.in"
    , "mk" -/- "install.mk.in", "mk" -/- "project.mk", "README"
    , "INSTALL" ]

-- | This auxiliary function gives us a top-level 'Filepath' that we can 'need'
-- for all libraries and programs that are needed for a complete build.
-- For libraries, it returns the path to the @.conf@ file in the package
-- database. For programs, it returns the path to the compiled executable.
pkgTarget :: Package -> Action FilePath
pkgTarget pkg
    | isLibrary pkg = pkgConfFile (vanillaContext Stage1 pkg)
    | otherwise     = programPath =<< programContext Stage1 pkg

wrapper :: FilePath -> String
wrapper "ghc"         = ghcWrapper
wrapper "ghc-pkg"     = ghcPkgWrapper
wrapper "ghci-script" = ghciScriptWrapper
wrapper "haddock"     = haddockWrapper
wrapper "hsc2hs"      = hsc2hsWrapper
wrapper "runghc"      = runGhcWrapper
wrapper _             = commonWrapper

-- | Wrapper scripts for different programs. Common is default wrapper.

ghcWrapper :: String
ghcWrapper = "exec \"$executablename\" -B\"$libdir\" ${1+\"$@\"}\n"

ghcPkgWrapper :: String
ghcPkgWrapper = unlines
    [ "PKGCONF=\"$libdir/package.conf.d\""
    , "exec \"$executablename\" --global-package-db \"$PKGCONF\" ${1+\"$@\"}" ]

haddockWrapper :: String
haddockWrapper = "exec \"$executablename\" -B\"$libdir\" -l\"$libdir\" ${1+\"$@\"}\n"

commonWrapper :: String
commonWrapper = "exec \"$executablename\" ${1+\"$@\"}\n"

hsc2hsWrapper :: String
hsc2hsWrapper = unlines
    [ "HSC2HS_EXTRA=\"--cflag=-fno-stack-protector\""
    , "tflag=\"--template=$libdir/template-hsc.h\""
    , "Iflag=\"-I$includedir/\""
    , "for arg do"
    , "    case \"$arg\" in"
    , "# On OS X, we need to specify -m32 or -m64 in order to get gcc to"
    , "# build binaries for the right target. We do that by putting it in"
    , "# HSC2HS_EXTRA. When cabal runs hsc2hs, it passes a flag saying which"
    , "# gcc to use, so if we set HSC2HS_EXTRA= then we don't get binaries"
    , "# for the right platform. So for now we just don't set HSC2HS_EXTRA="
    , "# but we probably want to revisit how this works in the future."
    , "#        -c*)          HSC2HS_EXTRA=;;"
    , "#        --cc=*)       HSC2HS_EXTRA=;;"
    , "        -t*)          tflag=;;"
    , "        --template=*) tflag=;;"
    , "        --)           break;;"
    , "    esac"
    , "done"
    , "exec \"$executablename\" ${tflag:+\"$tflag\"} $HSC2HS_EXTRA ${1+\"$@\"} \"$Iflag\"" ]

runGhcWrapper :: String
runGhcWrapper = "exec \"$executablename\" -f \"$exedir/ghc\" ${1+\"$@\"}\n"

-- | We need to ship ghci executable, which basically just calls ghc with
-- | --interactive flag.
ghciScriptWrapper :: String
ghciScriptWrapper = unlines
    [ "DIR=`dirname \"$0\"`"
    , "executable=\"$DIR/ghc\""
    , "exec $executable --interactive \"$@\"" ]

-- | When not on Windows, we want to ship the 3 flavours of the iserv program
--   in binary distributions. This isn't easily achievable by just asking for
--   the package to be built, since here we're generating 3 different
--   executables out of just one package, so we need to specify all 3 contexts
--   explicitly and 'need' the result of building them.
needIservBins :: Action ()
needIservBins = do
  rtsways <- interpretInContext (vanillaContext Stage1 ghc) getRtsWays
  need =<< traverse programPath
      [ Context Stage1 iserv w
      | w <- [vanilla, profiling, dynamic]
      , w `elem` rtsways
      ]
