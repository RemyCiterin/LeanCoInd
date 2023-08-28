import CoInd.Container


open Container in
class QPF (F:Type u → Type u) extends Functor F where
  C: Container.{u}
  abs: ∀ {α}, C.Obj α → F α
  repr: ∀ {α}, F α → C.Obj α
  abs_repr: ∀ {α} (x:F α), abs (repr x) = x
  abs_map: ∀ {α β} (f:α → β) (x:C.Obj α),
    abs (C.Map f x) = f <$> abs x


class IFunctor {I:Type u₁} (F: (I → Type u₁) → I → Type u₂) where
  imap : {α β: I → Type u₁} → (f:(i:I) → α i → β i) → {i:I} → F α i → F β i

open IContainer in
class IQPF {I:Type u₁} (F: (I → Type u₁) → I → Type u₁) extends IFunctor F where
  C: IContainer.{u₁} I
  abs: ∀ {α:I → Type u₁} {i:I}, C.Obj α i → F α i
  repr: ∀ {α: I → Type u₁} {i:I}, F α i → C.Obj α i
  abs_repr: ∀ {α: I → Type u₁} {i:I} (x:F α i), abs (repr x) = x
  abs_imap: ∀ {α β:I → Type u₁} (f:(i:I) → α i → β i) (x:C.Obj α i), abs (C.Map f x) = imap f (abs x)

