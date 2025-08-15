import Lean.Elab.DeclarationRange
import Lean.Elab.DeclModifiers
import Mathlib.New.Lean

/-!
This file defines attributes `iff_forw` and `iff_back` that expose either or both directions
of an 'iff' theorem as seperate theorems.
-/
-- see `Mathlib.Tactic.MkIffOfInductiveProp`
-- todo: automatically suggest when we want one of these theorems
-- todo: search for when we have used `decl_iff.mpr` rather than `decl` itself
--   (could just do text search for `_iff.mpr`)
-- todo: in hypothesis, split `∃`, `∧` into multiple hypothesis, eliminate `=`, etc.

namespace Mathlib.Tactic.IffToImp
  open Lean Meta Elab

inductive Direction where
  | forward
  | backward

-- could we handle e.g. annotations better?
def mkImpOfIff (iffName impName : Name) (impStx : Syntax) (dir : Direction) : CoreM Unit :=
  MetaM.run' do
  let info ← getConstInfo iffName
  forallTelescope info.type λ params type ↦ do
    let mkApp2 (.const ``Iff []) p q := type
      | throwError "the current declaration type is not an iff statement"
    let (dom, cod, proj) := match dir with
      | .forward  => (p, q, mkApp2 (.const ``Iff.mp  []) p q)
      | .backward => (q, p, mkApp2 (.const ``Iff.mpr []) p q)
    addDecl <| .thmDecl {
      name        := impName
      levelParams := info.levelParams
      type :=
        ←mkForallFVars params
          <| ←mkArrow' dom cod `h
      value :=
        ←mkLambdaFVars params
          <| proj.app
            <| mkAppN (.const iffName (info.levelParams.map .param)) params
    }
    -- consider the spesifics of the next two commands
    addDeclarationRangesFromSyntax impName (←getRef) impStx
    addConstInfo impStx impName

def convertName (iffName : String) (dir : Direction) : Option String := do
  if let some n := iffName.dropSuffix? "_iff" then
    if dir matches .backward then
      return n.toString
  -- TODO: more support
  throw ()

def getTargetDeclName
    (iffDeclName : Name) (providedShortName? : Option Name) (dir : Direction) : CoreM Name :=
  if let some providedShortName := providedShortName? then
    return (←mkDeclName
      (currNamespace := ←getCurrNamespace)
      (modifiers     := {})
      (shortName     := providedShortName)).1
  else do
    let .str ns iffName := iffDeclName | throwError "unexpected declaration name {iffDeclName}"
    return .str ns <| ←(convertName iffName dir).getDM
      (throwError "\
        the current name is not supported under this operation, \
        and an alternative name has not been provided")


-- docstrings here will appear when hovering over the attribute syntax itself,
-- but only when not overriden by `addConstInfo` above
syntax (name := iffForw) "iff_forw" (ppSpace ident)? : attr
syntax (name := iffBack) "iff_back" (ppSpace ident)? : attr

def addCore (dir : Direction)
    (iffDeclName : Name) (attrStx : Syntax) (attrKind : AttributeKind) : CoreM Unit := do
  unless attrKind == .global do
    throwError "the option '{attrKind}' is not valid with this attribute."
  let providedNameStx? ← (do match attrStx with
    | `(attr| iff_forw $n:ident)
    | `(attr| iff_back $n:ident) => return some n.raw
    | `(attr| iff_forw)
    | `(attr| iff_back)          => return none
    | _                          => throwError "unrecognized syntax")
  let targetDeclName ← getTargetDeclName iffDeclName (providedNameStx?.map (·.getId)) dir
  mkImpOfIff iffDeclName targetDeclName (providedNameStx?.getD attrStx) dir

initialize registerBuiltinAttribute {
  name  := `iffForw
  descr := "Generate a forward version of an 'iff' theorem."
  add   := addCore .forward
}

initialize registerBuiltinAttribute {
  name  := `iffBack
  descr := "Generate a backward version of an 'iff' theorem."
  add   := addCore .backward
}

end Mathlib.Tactic.IffToImp
