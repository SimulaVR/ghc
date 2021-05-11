{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- instance Diagnostic DsMessage

module GHC.HsToCore.Errors.Ppr where

import GHC.Builtin.Names (withDictName)
import GHC.Core.Predicate (isEvVar)
import GHC.Core.Type
import GHC.Core.Utils (exprType)
import GHC.Driver.Flags
import GHC.Hs
import GHC.HsToCore.Errors.Types
import GHC.Prelude
import GHC.Tc.Errors.Ppr (formatLevPolyErr)
import GHC.Types.Error
import GHC.Types.Id (idType)
import GHC.Types.SrcLoc
import GHC.Utils.Misc
import GHC.Utils.Outputable
import qualified GHC.LanguageExtensions as LangExt
import {-# SOURCE #-} GHC.HsToCore.Pmc.Ppr (pprUncovered) -- sad, but avoids cyclic deps


instance Diagnostic DsMessage where
  diagnosticMessage = \case
    DsUnknownMessage m
      -> diagnosticMessage m
    DsEmptyEnumeration
      -> mkSimpleDecorated $ text "Enumeration is empty"
    DsIdentitiesFound conv_fn type_of_conv
      -> mkSimpleDecorated $
           vcat [ text "Call of" <+> ppr conv_fn <+> dcolon <+> ppr type_of_conv
                , nest 2 $ text "can probably be omitted"
                ]
    DsOverflowedLiterals i tc bounds _possiblyUsingNegativeLiterals
      -> let msg = case bounds of
               Nothing
                 -> vcat [ text "Literal" <+> integer i
                       <+> text "is negative but" <+> ppr tc
                       <+> text "only supports positive numbers"
                         ]
               Just (MinBound minB, MaxBound maxB)
                 -> vcat [ text "Literal" <+> integer i
                                 <+> text "is out of the" <+> ppr tc <+> text "range"
                                 <+> integer minB <> text ".." <> integer maxB
                         ]
         in mkSimpleDecorated msg
    DsRedundantBangPatterns ctx q
      -> mkSimpleDecorated $ pprEqn ctx q "has redundant bang"
    DsOverlappingPatterns ctx q
      -> mkSimpleDecorated $ pprEqn ctx q "is redundant"
    DsInaccessibleRhs ctx q
      -> mkSimpleDecorated $ pprEqn ctx q "has inaccessible right hand side"
    DsMaxPmCheckModelsReached limit
      -> mkSimpleDecorated $ vcat
           [ hang
               (text "Pattern match checker ran into -fmax-pmcheck-models="
                 <> int limit
                 <> text " limit, so")
               2
               (  bullet <+> text "Redundant clauses might not be reported at all"
               $$ bullet <+> text "Redundant clauses might be reported as inaccessible"
               $$ bullet <+> text "Patterns reported as unmatched might actually be matched")
           ]
    DsNonExhaustivePatterns kind _flag maxPatterns vars nablas
      -> mkSimpleDecorated $
           pprContext False kind (text "are non-exhaustive") $ \_ ->
             case vars of -- See #11245
                  [] -> text "Guards do not cover entire pattern space"
                  _  -> let us = map (\nabla -> pprUncovered nabla vars) nablas
                            pp_tys = pprQuotedList $ map idType vars
                        in  hang
                              (text "Patterns of type" <+> pp_tys <+> text "not matched:")
                              4
                              (vcat (take maxPatterns us) $$ dots maxPatterns us)
    DsTopLevelBindsNotAllowed bindsType bind
      -> let desc = case bindsType of
               UnliftedTypeBinds -> "bindings for unlifted types"
               StrictBinds       -> "strict bindings"
         in mkSimpleDecorated $
              hang (text "Top-level" <+> text desc <+> text "aren't allowed:") 2 (ppr bind)
    DsUselessSpecialiseForClassMethodSelector poly_id
      -> mkSimpleDecorated $
           text "Ignoring useless SPECIALISE pragma for NOINLINE function:" <+> quotes (ppr poly_id)
    DsUselessSpecialiseForNoInlineFunction poly_id
      -> mkSimpleDecorated $
          text "Ignoring useless SPECIALISE pragma for NOINLINE function:" <+> quotes (ppr poly_id)
    DsMultiplicityCoercionsNotSupported
      -> mkSimpleDecorated $ text "Multiplicity coercions are currently not supported"
    DsOrphanRule rule
      -> mkSimpleDecorated $ text "Orphan rule:" <+> ppr rule
    DsRuleLhsTooComplicated orig_lhs lhs2
      -> mkSimpleDecorated $
           hang (text "RULE left-hand side too complicated to desugar")
                      2 (vcat [ text "Optimised lhs:" <+> ppr lhs2
                              , text "Orig lhs:" <+> ppr orig_lhs])
    DsRuleIgnoredDueToConstructor con
      -> mkSimpleDecorated $ vcat
           [ text "A constructor," <+> ppr con <>
               text ", appears as outermost match in RULE lhs."
           , text "This rule will be ignored." ]
    DsRuleBindersNotBound unbound orig_bndrs orig_lhs lhs2
      -> mkSimpleDecorated $ vcat (map pp_dead unbound)
         where
           pp_dead bndr =
             hang (sep [ text "Forall'd" <+> pp_bndr bndr
                       , text "is not bound in RULE lhs"])
                2 (vcat [ text "Orig bndrs:" <+> ppr orig_bndrs
                        , text "Orig lhs:" <+> ppr orig_lhs
                        , text "optimised lhs:" <+> ppr lhs2 ])

           pp_bndr b
            | isTyVar b = text "type variable" <+> quotes (ppr b)
            | isEvVar b = text "constraint"    <+> quotes (ppr (varType b))
            | otherwise = text "variable"      <+> quotes (ppr b)
    DsMultipleConForNewtype names
      -> mkSimpleDecorated $ text "Multiple constructors for newtype:" <+> pprQuotedList names
    DsLazyPatCantBindVarsOfUnliftedType unlifted_bndrs
      -> mkSimpleDecorated $
          hang (text "A lazy (~) pattern cannot bind variables of unlifted type." $$
                text "Unlifted variables:")
             2 (vcat (map (\id -> ppr id <+> dcolon <+> ppr (idType id)) unlifted_bndrs))
    DsNotYetHandledByTH reason
      -> case reason of
             ThAmbiguousRecordUpdates fld
               -> mkMsg "Ambiguous record updates" (ppr fld)
             ThAbstractClosedTypeFamily decl
               -> mkMsg "abstract closed type family" (ppr decl)
             ThForeignLabel cls
               -> mkMsg "Foreign label" (doubleQuotes (ppr cls))
             ThForeignExport decl
               -> mkMsg "Foreign export" (ppr decl)
             ThMinimalPragmas
               -> mkMsg "MINIMAL pragmas" empty
             ThSCCPragmas
               -> mkMsg "SCC pragmas" empty
             ThNoUserInline
               -> mkMsg "NOUSERINLINE" empty
             ThExoticFormOfType ty
               -> mkMsg "Exotic form of type" (ppr ty)
             ThAmbiguousRecordSelectors e
               -> mkMsg "Ambiguous record selectors" (ppr e)
             ThMonadComprehensionSyntax e
               -> mkMsg "monad comprehension and [: :]" (ppr e)
             ThCostCentres e
               -> mkMsg "Cost centres" (ppr e)
             ThExpressionForm e
               -> mkMsg "Expression form" (ppr e)
             ThExoticStatement other
               -> mkMsg "Exotic statement" (ppr other)
             ThExoticLiteral lit
               -> mkMsg "Exotic literal" (ppr lit)
             ThExoticPattern pat
               -> mkMsg "Exotic pattern" (ppr pat)
             ThGuardedLambdas m
               -> mkMsg "Guarded lambdas" (pprMatch m)
             ThNegativeOverloadedPatterns pat
               -> mkMsg "Negative overloaded patterns" (ppr pat)
             ThHaddockDocumentation
               -> mkMsg "Haddock documentation" empty
             ThWarningAndDeprecationPragmas decl
               -> mkMsg "WARNING and DEPRECATION pragmas" $
                    text "Pragma for declaration of" <+> ppr decl
             ThDefaultDeclarations decl
               -> mkMsg "Default declarations" (ppr decl)
             ThSplicesWithinDeclBrackets
               -> mkMsg "Splices within declaration brackets" empty
         where
           mkMsg what doc =
             mkSimpleDecorated $
               hang (text what <+> text "not (yet) handled by Template Haskell") 2 doc
    DsAggregatedViewExpressions views
      -> mkSimpleDecorated (vcat msgs)
         where
           msgs = map (\g -> text "Putting these view expressions into the same case:" <+> (ppr g)) views
    DsUnbangedStrictPatterns bind
      -> mkSimpleDecorated $
           hang (text "Pattern bindings containing unlifted types should use" $$
                 text "an outermost bang pattern:")
              2 (ppr bind)
    DsCannotMixPolyAndUnliftedBindings bind
      -> mkSimpleDecorated $
           hang (text "You can't mix polymorphic and unlifted bindings:")
              2 (ppr bind)
    DsInvalidInstantiationDictAtType wrapped_ty
      -> mkSimpleDecorated $
           hang (text "Invalid instantiation of" <+>
                quotes (ppr withDictName) <+> text "at type:")
             4 (ppr wrapped_ty)
    DsWrongDoBind _rhs elt_ty
      -> mkSimpleDecorated $ badMonadBind elt_ty
    DsUnusedDoBind _rhs elt_ty
      -> mkSimpleDecorated $ badMonadBind elt_ty
    DsRecBindsNotAllowedForUnliftedTys binds
      -> mkSimpleDecorated $
           hang (text "Recursive bindings for unlifted types aren't allowed:")
              2 (vcat (map ppr binds))
    DsLevityPolyInExpr e prov
      -> let extra = case prov of
               LevityCheckHsExpr hsExpr -> ppr hsExpr
               LevityCheckWpFun doc     -> doc

         in mkSimpleDecorated $
               formatLevPolyErr (exprType e) $$ (text "In the type of expression:" <+> extra)
    DsLevityPolyInType ty prov
      -> let extra = case prov of
               LevityCheckInBinder v
                 -> text "In the type of binder" <+> quotes (ppr v)
               LevityCheckInVarType
                 -> text "When trying to create a variable of type:" <+> ppr ty
               LevityCheckInWildcardPattern
                 -> text "In a wildcard pattern"
               LevityCheckInUnboxedTuplePattern p
                 -> text "In the type of an element of an unboxed tuple pattern:" $$ ppr p
               LevityCheckGenSig
                 -> empty
               LevityCheckCmdStmt
                 -> empty
               LevityCheckMkCmdEnv id_var
                 -> text "In the result of the function" <+> quotes (ppr id_var)
               LevityCheckDoCmd do_block
                 -> text "In the do-command:" <+> ppr do_block
               LevityCheckDesugaringCmd cmd
                 -> text "When desugaring the command:" <+> ppr cmd
               LevityCheckInCmd body
                 -> text "In the command:" <+> ppr body
               LevityCheckInFunUse using
                 -> text "In the result of a" <+> quotes (text "using") <+> text "function:" <+> ppr using
        in mkSimpleDecorated $ formatLevPolyErr ty $$ extra

  diagnosticReason = \case
    DsUnknownMessage m          -> diagnosticReason m
    DsEmptyEnumeration          -> WarningWithFlag Opt_WarnEmptyEnumerations
    DsIdentitiesFound{}         -> WarningWithFlag Opt_WarnOverflowedLiterals
    DsOverflowedLiterals{}      -> WarningWithFlag Opt_WarnOverflowedLiterals
    DsRedundantBangPatterns{}   -> WarningWithFlag Opt_WarnRedundantBangPatterns
    DsOverlappingPatterns{}     -> WarningWithFlag Opt_WarnOverlappingPatterns
    DsInaccessibleRhs{}         -> WarningWithFlag Opt_WarnOverlappingPatterns
    DsMaxPmCheckModelsReached{} -> WarningWithoutFlag
    DsNonExhaustivePatterns _ (ExhaustivityCheckType mb_flag) _ _ _
      -> maybe WarningWithoutFlag WarningWithFlag mb_flag
    DsTopLevelBindsNotAllowed{}                 -> ErrorWithoutFlag
    DsUselessSpecialiseForClassMethodSelector{} -> WarningWithoutFlag
    DsUselessSpecialiseForNoInlineFunction{}    -> WarningWithoutFlag
    DsMultiplicityCoercionsNotSupported{}       -> ErrorWithoutFlag
    DsOrphanRule{}                              -> WarningWithFlag Opt_WarnOrphans
    DsRuleLhsTooComplicated{}                   -> WarningWithoutFlag
    DsRuleIgnoredDueToConstructor{}             -> WarningWithoutFlag
    DsRuleBindersNotBound{}                     -> WarningWithoutFlag
    DsMultipleConForNewtype{}                   -> ErrorWithoutFlag
    DsLazyPatCantBindVarsOfUnliftedType{}       -> ErrorWithoutFlag
    DsNotYetHandledByTH{}                       -> ErrorWithoutFlag
    DsAggregatedViewExpressions{}               -> WarningWithoutFlag
    DsUnbangedStrictPatterns{}                  -> WarningWithFlag Opt_WarnUnbangedStrictPatterns
    DsCannotMixPolyAndUnliftedBindings{}        -> ErrorWithoutFlag
    DsInvalidInstantiationDictAtType{}          -> ErrorWithoutFlag
    DsWrongDoBind{}                             -> WarningWithFlag Opt_WarnWrongDoBind
    DsUnusedDoBind{}                            -> WarningWithFlag Opt_WarnUnusedDoBind
    DsRecBindsNotAllowedForUnliftedTys{}        -> ErrorWithoutFlag
    DsLevityPolyInExpr{}                        -> ErrorWithoutFlag
    DsLevityPolyInType{}                        -> ErrorWithoutFlag

  diagnosticHints  = \case
    DsUnknownMessage m          -> diagnosticHints m
    DsEmptyEnumeration          -> noHints
    DsIdentitiesFound{}         -> noHints
    DsOverflowedLiterals i _tc bounds usingNegLiterals
      -> case (bounds, usingNegLiterals) of
          (Just (MinBound minB, MaxBound _), NotUsingNegLiterals)
            | minB == -i -- Note [Suggest NegativeLiterals]
            , i > 0 -> [SuggestExtension LangExt.NegativeLiterals]
          _ -> noHints
    DsRedundantBangPatterns{}                   -> noHints
    DsOverlappingPatterns{}                     -> noHints
    DsInaccessibleRhs{}                         -> noHints
    DsMaxPmCheckModelsReached{}                 -> [SuggestIncreaseMaxPmCheckModels]
    DsNonExhaustivePatterns{}                   -> noHints
    DsTopLevelBindsNotAllowed{}                 -> noHints
    DsUselessSpecialiseForClassMethodSelector{} -> noHints
    DsUselessSpecialiseForNoInlineFunction{}    -> noHints
    DsMultiplicityCoercionsNotSupported         -> noHints
    DsOrphanRule{}                              -> noHints
    DsRuleLhsTooComplicated{}                   -> noHints
    DsRuleIgnoredDueToConstructor{}             -> noHints
    DsRuleBindersNotBound{}                     -> noHints
    DsMultipleConForNewtype{}                   -> noHints
    DsLazyPatCantBindVarsOfUnliftedType{}       -> noHints
    DsNotYetHandledByTH{}                       -> noHints
    DsAggregatedViewExpressions{}               -> noHints
    DsUnbangedStrictPatterns{}                  -> noHints
    DsCannotMixPolyAndUnliftedBindings{}        -> [SuggestAddTypeSignature]
    DsWrongDoBind rhs _                         -> [SuggestBindToWildcard rhs]
    DsUnusedDoBind rhs _                        -> [SuggestBindToWildcard rhs]
    DsRecBindsNotAllowedForUnliftedTys{}        -> noHints
    DsInvalidInstantiationDictAtType{}          -> noHints
    DsLevityPolyInExpr{}                        -> noHints
    DsLevityPolyInType{}                        -> noHints

--
-- Helper functions
--

badMonadBind :: Type -> SDoc
badMonadBind elt_ty
  = hang (text "A do-notation statement discarded a result of type")
       2 (quotes (ppr elt_ty))

-- Print a single clause (for redundant/with-inaccessible-rhs)
pprEqn :: HsMatchContext GhcRn -> SDoc -> String -> SDoc
pprEqn ctx q txt = pprContext True ctx (text txt) $ \f ->
  f (q <+> matchSeparator ctx <+> text "...")

pprContext :: Bool -> HsMatchContext GhcRn -> SDoc -> ((SDoc -> SDoc) -> SDoc) -> SDoc
pprContext singular kind msg rest_of_msg_fun
  = vcat [text txt <+> msg,
          sep [ text "In" <+> ppr_match <> char ':'
              , nest 4 (rest_of_msg_fun pref)]]
  where
    txt | singular  = "Pattern match"
        | otherwise = "Pattern match(es)"

    (ppr_match, pref)
        = case kind of
             FunRhs { mc_fun = L _ fun }
                  -> (pprMatchContext kind, \ pp -> ppr fun <+> pp)
             _    -> (pprMatchContext kind, \ pp -> pp)

dots :: Int -> [a] -> SDoc
dots maxPatterns qs
    | qs `lengthExceeds` maxPatterns = text "..."
    | otherwise                      = empty
