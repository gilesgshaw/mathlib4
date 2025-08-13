import Lean.Parser.Command

/-

Possible improvements to `mkArrow` (as furthered by definition below):
* explanation of (non-)significance of name, and handling of loose bound variables
* automatically gives proofs name 'h' vs 'x'
* ability to spesify a suggested name
* choice of which algorithm to use (`getUnusedName` or `mkFreshUserName`)
* should we live in `Core` or `Meta`? If Core, should we handle loose bound variables?
* make sure `mkArrowN` is suitably updated

-/

/--
A variant on `mkArrow`. Whereas the aformentioned uses `mkFreshUserName` to generate a globally
unique but inaccessible name, this method uses `LocalContext.getUnusedName` to generate an
accessible user name, which is only garunteed to be unused in the current local context.
-/
def Lean.mkArrow' (dom cod : Expr) (suggestedName := `x) : MetaM Expr :=
  return .forallE
    (binderName := (←getLCtx).getUnusedName suggestedName)
    (binderInfo := .default)
    (binderType := dom)
    (body       := cod)
