-- | Dependencies and Usage of a module
module GHC.Unit.Module.Deps
   ( Dependencies (..)
   , Usage (..)
   , noDependencies
   )
where

import GHC.Prelude

import GHC.Types.SafeHaskell
import GHC.Types.Name
import GHC.Unit.Module.Name
import GHC.Unit.Module

import GHC.Utils.Fingerprint
import GHC.Utils.Binary

-- | Dependency information about ALL modules and packages below this one
-- in the import hierarchy.
--
-- Invariant: the dependencies of a module @M@ never includes @M@.
--
-- Invariant: none of the lists contain duplicates.
--
-- See Note [Transitive Information in Dependencies]
data Dependencies = Deps
   { dep_direct_mods :: [ModuleNameWithIsBoot]
      -- ^ All home-package modules which are directly imported by this one.

   , dep_direct_pkgs :: [UnitId]
      -- ^ All packages directly imported by this module
      -- I.e. packages to which this module's direct imports belong.
      --
   , dep_plgins :: [ModuleName]
      -- ^ All the plugins used while compiling this module.


    -- Transitive information below here
   , dep_trusted_pkgs :: [UnitId]
      -- Packages which we are required to trust
      -- when the module is imported as a safe import
      -- (Safe Haskell). See Note [Tracking Trust Transitively] in GHC.Rename.Names

   , dep_source_mods :: [ModuleNameWithIsBoot]
      -- ^ All modules which have boot files below this one, and whether we
      -- should use the boot file or not.
      -- This information is only used to populate the eps_is_boot field.

   , dep_orphs  :: [Module]
      -- ^ Transitive closure of orphan modules (whether
      -- home or external pkg).
      --
      -- (Possible optimization: don't include family
      -- instance orphans as they are anyway included in
      -- 'dep_finsts'.  But then be careful about code
      -- which relies on dep_orphs having the complete list!)
      -- This does NOT include us, unlike 'imp_orphs'.

   , dep_finsts :: [Module]
      -- ^ Transitive closure of depended upon modules which
      -- contain family instances (whether home or external).
      -- This is used by 'checkFamInstConsistency'.  This
      -- does NOT include us, unlike 'imp_finsts'. See Note
      -- [The type family instance consistency story].

   }
   deriving( Eq )
        -- Equality used only for old/new comparison in GHC.Iface.Recomp.addFingerprints
        -- See 'GHC.Tc.Utils.ImportAvails' for details on dependencies.

instance Binary Dependencies where
    put_ bh deps = do put_ bh (dep_direct_mods deps)
                      put_ bh (dep_direct_pkgs deps)
                      put_ bh (dep_trusted_pkgs deps)
                      put_ bh (dep_source_mods deps)
                      put_ bh (dep_orphs deps)
                      put_ bh (dep_finsts deps)
                      put_ bh (dep_plgins deps)

    get bh = do dms <- get bh
                dps <- get bh
                tps <- get bh
                sms <- get bh
                os <- get bh
                fis <- get bh
                pl <- get bh
                return (Deps { dep_direct_mods = dms
                             , dep_direct_pkgs = dps
                             , dep_source_mods = sms
                             , dep_trusted_pkgs = tps
                             , dep_orphs = os,
                               dep_finsts = fis, dep_plgins = pl })

noDependencies :: Dependencies
noDependencies = Deps [] [] [] [] [] [] []

-- | Records modules for which changes may force recompilation of this module
-- See wiki: https://gitlab.haskell.org/ghc/ghc/wikis/commentary/compiler/recompilation-avoidance
--
-- This differs from Dependencies.  A module X may be in the dep_mods of this
-- module (via an import chain) but if we don't use anything from X it won't
-- appear in our Usage
data Usage
  -- | Module from another package
  = UsagePackageModule {
        usg_mod      :: Module,
           -- ^ External package module depended on
        usg_mod_hash :: Fingerprint,
            -- ^ Cached module fingerprint
        usg_safe :: IsSafeImport
            -- ^ Was this module imported as a safe import
    }
  -- | Module from the current package
  | UsageHomeModule {
        usg_mod_name :: ModuleName,
            -- ^ Name of the module
        usg_mod_hash :: Fingerprint,
            -- ^ Cached module fingerprint
        usg_entities :: [(OccName,Fingerprint)],
            -- ^ Entities we depend on, sorted by occurrence name and fingerprinted.
            -- NB: usages are for parent names only, e.g. type constructors
            -- but not the associated data constructors.
        usg_exports  :: Maybe Fingerprint,
            -- ^ Fingerprint for the export list of this module,
            -- if we directly imported it (and hence we depend on its export list)
        usg_safe :: IsSafeImport
            -- ^ Was this module imported as a safe import
    }                                           -- ^ Module from the current package
  -- | A file upon which the module depends, e.g. a CPP #include, or using TH's
  -- 'addDependentFile'
  | UsageFile {
        usg_file_path  :: FilePath,
        -- ^ External file dependency. From a CPP #include or TH
        -- addDependentFile. Should be absolute.
        usg_file_hash  :: Fingerprint
        -- ^ 'Fingerprint' of the file contents.

        -- Note: We don't consider things like modification timestamps
        -- here, because there's no reason to recompile if the actual
        -- contents don't change.  This previously lead to odd
        -- recompilation behaviors; see #8114
  }
  -- | A requirement which was merged into this one.
  | UsageMergedRequirement {
        usg_mod :: Module,
        usg_mod_hash :: Fingerprint
  }
    deriving( Eq )
        -- The export list field is (Just v) if we depend on the export list:
        --      i.e. we imported the module directly, whether or not we
        --           enumerated the things we imported, or just imported
        --           everything
        -- We need to recompile if M's exports change, because
        -- if the import was    import M,       we might now have a name clash
        --                                      in the importing module.
        -- if the import was    import M(x)     M might no longer export x
        -- The only way we don't depend on the export list is if we have
        --                      import M()
        -- And of course, for modules that aren't imported directly we don't
        -- depend on their export lists

instance Binary Usage where
    put_ bh usg@UsagePackageModule{} = do
        putByte bh 0
        put_ bh (usg_mod usg)
        put_ bh (usg_mod_hash usg)
        put_ bh (usg_safe     usg)

    put_ bh usg@UsageHomeModule{} = do
        putByte bh 1
        put_ bh (usg_mod_name usg)
        put_ bh (usg_mod_hash usg)
        put_ bh (usg_exports  usg)
        put_ bh (usg_entities usg)
        put_ bh (usg_safe     usg)

    put_ bh usg@UsageFile{} = do
        putByte bh 2
        put_ bh (usg_file_path usg)
        put_ bh (usg_file_hash usg)

    put_ bh usg@UsageMergedRequirement{} = do
        putByte bh 3
        put_ bh (usg_mod      usg)
        put_ bh (usg_mod_hash usg)

    get bh = do
        h <- getByte bh
        case h of
          0 -> do
            nm    <- get bh
            mod   <- get bh
            safe  <- get bh
            return UsagePackageModule { usg_mod = nm, usg_mod_hash = mod, usg_safe = safe }
          1 -> do
            nm    <- get bh
            mod   <- get bh
            exps  <- get bh
            ents  <- get bh
            safe  <- get bh
            return UsageHomeModule { usg_mod_name = nm, usg_mod_hash = mod,
                     usg_exports = exps, usg_entities = ents, usg_safe = safe }
          2 -> do
            fp   <- get bh
            hash <- get bh
            return UsageFile { usg_file_path = fp, usg_file_hash = hash }
          3 -> do
            mod <- get bh
            hash <- get bh
            return UsageMergedRequirement { usg_mod = mod, usg_mod_hash = hash }
          i -> error ("Binary.get(Usage): " ++ show i)


{-
Note [Transitive Information in Dependencies]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is important to be careful what information we put in 'Dependencies' because
ultimately it ends up serialised in an interface file. Interface files must always
be kept up-to-date with the state of the world, so if `Dependencies` needs to be updated
then the module had to be recompiled just to update `Dependencies`.

Before #16885, the dependencies used to contain the transitive closure of all
home modules. Therefore, if you added an import somewhere low down in the home package
it would recompile nearly module in your project, just to update this information.

Now, we are a bit more careful about what we store and explicitly store the transitive
information if it's really needed.

# Direct Information

* dep_direct_mods - Directly imported home package modules
* dep_direct_pkgs - Directly imported packages
* dep_plgins      - Directly used plugins

# Transitive Information

Some features of the compiler require transitive information about what is currently
being compiled, so that is explicitly stored separately in the form they need.

* dep_trusted_pkgs - Only used for the -fpackage-trust feature
* dep_source_mods  - Only used to populate eps_is_boot in -c mode
* dep_orphs        - Modules with orphan instances
* dep_finsts       - Modules with type family instances

Important note: If you add some transitive information to the interface file then
you need to make sure recompilation is triggered when it could be out of date.
The correct way to do this is to include the transitive information in the export
hash of the module. The export hash is computed in `GHC.Iface.Recomp.addFingerprints`.
-}
