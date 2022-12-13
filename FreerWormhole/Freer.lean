--
-- A basic freer monad. Based on various haskell libraries including freer-simple and
-- the paper "Freer Monads, More Extensible Effects" by Oleg Kiselyov and Hiromi Ishii
--

-- The Freer monad doesn't contain actual executable code, but instead
-- stores either a result value (Pure) or an effect plus continuation (Impure).
--

import FreerWormhole.WType

open pfunctor W_type

structure Effect : Type (u+1) where
   (op : Type u)
   (ret : op → Type u)

inductive OU : List Effect.{u} → Type u → Type (u+1) where
| Leaf {eff : Effect.{u}} {effs : List Effect.{u}} : (c : eff.op) → OU (eff :: effs) (eff.ret c)
| Node {eff : Effect} {effs : List Effect} : OU effs x → OU (eff :: effs) x

class HasEffect (e : Effect) (effs : List Effect) where
    inject : (c : e.op) → OU effs (e.ret c)

instance : HasEffect e (e :: effs) where
    inject := fun c => @OU.Leaf e effs c

instance [HasEffect e effs] : HasEffect e (z :: effs) where
    inject := fun x => OU.Node (@HasEffect.inject e effs _ x)



inductive EffWA.{u} (effs : List Effect.{u}) (α : Type u) : Type (u+1) where
    | Pure : α → EffWA effs α 
    | Impure : (x : Type u) → OU effs x → EffWA effs α -- the (x → W ..) part is in the second part of the pfunctor (EffWB)


def EffWB.{u} {effs : List Effect.{u}} {α : Type u} : EffWA effs α → Type (u+1)
    | .Pure a      => ULift <| Fin 0 -- can't use False since we need a Type here, not a Prop
    | .Impure x gx => ULift.{u+1,u} x

def EffWPF.{u} (effs : List Effect) (α : Type u) : pfunctor.{u+1,u+1} := pfunctor.mk (EffWA.{u} effs α) EffWB.{u}

structure EffW.{u} (effs : List Effect.{u}) (a : Type u) : Type (u+1) where
   val : W (EffWPF.{u} effs a)


-- lift into EffW
def sendEffW.{u} {g : Effect.{u}} {effs : List Effect.{u}} [HasEffect g effs] (ga : g.op) : EffW effs (g.ret ga) :=
    EffW.mk <| ⟨EffWA.Impure (g.ret ga) (HasEffect.inject ga), fun a => W.mk ⟨EffWA.Pure <| ULift.down a, Fin.elim0 ∘ ULift.down⟩⟩



def EffWAlg.{u} (effs : List Effect.{u}) (a : Type (u+1)) := {x : Type u} → (c : OU effs x) → (x → a) → a

/-
-- "normal" bind for EffW using structural recursion

def bindRawW {effs : List Effect} {α β : Type} : W (EffWPF effs α) → (α → W (EffWPF effs β)) → W (EffWPF effs β) := fun m1 m2 =>
    match m1 with
    | ⟨EffWA.Pure a,     _⟩ => m2 a
    | ⟨EffWA.Impure x ou, bx⟩ => W.mk ⟨EffWA.Impure x ou, fun x => (@bindRawW effs α β (bx x) m2)⟩

def bindEffW {α β : Type} : EffW g α → (α → EffW g β) → EffW g β := fun m1 m2 =>
    -- we just strip off the FreerIxW wrapper and recurse
    EffW.mk <| bindRawW m1.val (fun x => (m2 x).val)
-/

/-
-- alternate implementation of bind using a fold, similar to the "Hefty Algebras" paper
--
-- ugh, so much universe manipulation
-/
def foldOver.{u} {a : Type u} {b : Type (u+1)} {effs : List Effect.{u}} (pf : a → b) (alg : EffWAlg effs b) (w : EffW effs a) : b :=
    let walg : (Σ (x : EffWA effs a), (@EffWB effs a) x → b) → b := fun d =>
        match d with
        | ⟨EffWA.Pure a, z⟩ => pf a
        | ⟨EffWA.Impure x gx, next⟩ => @alg x gx (fun z => next (ULift.up.{u+1,u} z))
    let wpf := EffWPF.{u} effs a
    let v : W_type wpf.B := w.val
    @W_type.elim.{u+1,u+1} wpf.A wpf.B _ walg v
    --W_type.elim.{u+1} walg v


def bindEffW {effs : List Effect.{u}} (m : EffW effs a) (f : a → EffW effs b) : EffW effs b :=
    let bindAlg {x : Type u} : OU effs x → (x → EffW effs b)  → EffW effs b :=
        fun ou next => EffW.mk ⟨EffWA.Impure _ ou, fun v => EffW.val <| next (ULift.down.{u+1,u} v)⟩
    @foldOver a (EffW effs b) effs f bindAlg m


-- pure for EffW
def pureEffW {α : Type} (a : α) : EffW effs α := EffW.mk ⟨EffWA.Pure a, Fin.elim0 ∘ ULift.down⟩


instance : Monad (EffW effs) where
    pure := pureEffW
    bind := bindEffW

--
-- EffW as a Functor
--

def EffWMap (f : α → β) (w : EffW effs α) : EffW effs β :=
    let Walg := fun d =>
        match d with
        | ⟨EffWA.Pure a, z⟩         => W.mk ⟨EffWA.Pure (f a), z⟩
        | ⟨EffWA.Impure x gx, next⟩ => W.mk ⟨EffWA.Impure x gx, next⟩
    EffW.mk <| W_type.elim Walg w.val

instance : Functor (EffW effs) :=
    { map := EffWMap }


structure Handler (a b : Type u) (e : Effect.{u}) (effs : List Effect.{u}) (inp : Type u) where
   (ret : a → inp → EffW effs b)
   (handle : EffWAlg (e :: effs) (inp → EffW effs b))

-- Interpret a Freer monad. You must provide an "interpreter" which takes commands of type c
-- and produces monads of the final type n.  This runs the interpreter on a command
-- in the Impure constructor and combines it with the next chunk of the Freer monad
-- by using a definition of bind for the final monad n.
def handleEffW {a b : Type u} {e : Effect} {effs : List Effect} {inp : Type u} 
    (handler : Handler a b e effs inp) (m : EffW (e :: effs) a) : inp → EffW effs b :=
    foldOver handler.ret handler.handle m


--
-- higher-order effects
--

structure HEffect : Type (u+1) where
    (cmd : Type u)
    (fork : cmd  → Effect.{u})
    (ret : cmd → Type u)


--inductive Hefty : List HEffect → List HEffect → Type u → Type (u+1) where
--| Pure : a → Hefty h h a
--| Impure : OUH h h x → (x → Hefty h h a) → Hefty h h a

-- OUH needs two HEffect lists: one tracks the effs that can be witnessed, and gradually
-- gets shorted as we walk through .Node constructors. The second list tracks the type of the
-- HEffect list that gets returned from the fork functions. This second list is the "original" row
-- o HEffects and does not get shorted as we walk down the .Node constructors. The two lists
-- should be equal when referenced in a Hefty.Impure constructor.
inductive HOU.{u} : List HEffect → (cmd : Type u) → Effect.{u} → Type (u+1) where
    | Leaf : (c : heff.cmd) → HOU (heff :: heffs) (heff.ret c) (heff.fork c)
    | Node : HOU heffs c heff → HOU (_ :: heffs) c heff


inductive HEffWA.{u} (heffs : List HEffect.{u}) (α : Type u) : Type (u+1) where
    | Pure : α → HEffWA heffs α 
    | Impure : {heff : HEffect} → (x : Type u) → HOU effs heff → HEffWA heffs α -- the (x → W ..) part is in the second part of the pfunctor (EffWB)


def HEffWB.{u} {heffs : List HEffect.{u}} {α : Type u} : HEffWA heffs α → Type (u+1)
    | .Pure a      => ULift <| Fin 0 -- can't use False since we need a Type here, not a Prop
    | @HEffWA.Impure _ _ _ heff x hou => ULift.{u+1,u} x

def HEffWPF.{u} (heffs : List HEffect) (α : Type u) : pfunctor.{u+1,u+1} := pfunctor.mk (HEffWA.{u} heffs α) HEffWB.{u}

structure HEffW.{u} (heffs : List HEffect.{u}) (a : Type u) : Type (u+1) where
   val : W (HEffWPF.{u} heffs a)



((a : (heff.fork c).op) → Hefty alleffs alleffs ((heff.fork c).ret a)) → 

inductive Hefty2 (alleffs : List HEffect) : List HEffect → Type u → Type (u+2) where
| Pure : a → Hefty2 alleffs alleffs a
| Leaf : (heff : HEffect) → (c : heff.cmd) → ((a : (heff.fork c).op) → Hefty2 alleffs alleffs ((heff.fork c).ret a)) → (heff.ret c → Hefty2 alleffs (heff :: heffs) (heff.ret c)) → Hefty2 alleffs (heff :: heffs) (heff.ret c)
| Node : Hefty2 alleffs heffs a → Hefty2 alleffs (heff :: heffs) a


class HasHEffect (h : HEffect) (heffs : List HEffect) (alleffs : List HEffect) where
    inject : (c : h.cmd) → ((a : (h.fork c).op) → Hefty alleffs alleffs ((h.fork c).ret a)) → OUH heffs alleffs (h.ret c)

instance : HasHEffect h (h :: heffs) alleffs where
    inject := fun c k => @OUH.Leaf alleffs h heffs c k

instance [HasHEffect h heffs alleffs] : HasHEffect h (z :: heffs) alleffs where
    inject := fun c k => OUH.Node (@HasHEffect.inject h heffs alleffs _ c k)

#check WellFounded

def HeftyAlg (heffs : List HEffect) (a : Type u) := {x : Type u} → (c : OUH heffs heffs x) → (x → a) → a

def Hefty2Alg (a : Type u) := (heff : HEffect) → (c : heff.cmd) → (heff.ret c → a) → a

def hFold2 {a : Type u} {b : Type u} {heffs alleffs : List HEffect} (pf : a → b) (alg : Hefty2Alg b) : Hefty2 alleffs heffs a → b
| .Pure a => pf a
| @Hefty2.Leaf _ heff _ cx fo k => alg _ cx (fun x => hFold2 pf alg (k x))
| Hefty2.Node h' => hFold2 pf alg h'
    termination_by hFold2 p a h => h


def hPure (val : a) : Hefty h a := .Pure val

def freerBind (m : Freer effs a) (f : a → Freer effs b) : Freer effs b := @foldOver a (Freer effs b) effs f .Impure m
def hBind (m : Hefty h a) (f : a → Hefty h b) : Hefty h b :=
    match m with
    | .Pure a => f a
    | .Impure ou next => .Impure ou (fun x => hBind (next x) f)

def hLifted (eff : Type u → Type u) : HEffect := HEffect.mk eff (fun z c => Id) (fun z e => z)

def hLift {eff : Type u → Type u} {a : Type u} (f : Freer eff a ) : Hefty (hLifted eff) a :=
    match f with
    | .Pure a => hPure a
    | .Impure cz next => @Hefty.Impure (hLifted eff) a _ cz (fun x v => hPure v) (fun z => hLift (next z))


inductive CatchOp (a : Type u) : Type (u) where
| Catch : CatchOp a

inductive ThrowEff : Type u → Type u where
| Throw : ThrowEff a

inductive ExceptResult (a : Type u) : Type u where
| Success : ExceptResult a
| Failure : ExceptResult a

def CatchHEff : HEffect := HEffect.mk CatchOp (fun z op => ExceptResult) (fun z e => z)

def hCatch (m : (x : Type) → Hefty CatchHEff x) (err : (x : Type) → Hefty CatchHEff x) : Hefty CatchHEff a :=
    @Hefty.Impure CatchHEff a _ (@CatchOp.Catch a)
             (fun x fork => match fork with
                            | .Success => m x
                            | .Failure => err x)
             (fun z => hPure z)

-- an algebra for Hefty h a
def algH (h : HEffect) (f : Type u → Type (u+1)) : Type (u+1):=
    {a : Type u} → {z : Type u} → (op : h.cmd z) → (∀x, h.fork z op x → f x) → (h.ret z op → f a) → f a

def cataH (pf : {x : Type} → x → f x) (alg : algH h f) (t : Hefty h a) : f a :=
    match t with
    | Hefty.Pure x => pf x
    | Hefty.Impure c k next => alg c (fun x g => cataH pf alg (k x g)) (fun x => cataH pf alg (next x))

def Elaboration (h : HEffect) (eff : Type u → Type u) : Type (u+1) := algH h (Freer eff)

def elaborate (e : Elaboration h eff) (h : Hefty h a) : Freer eff a := cataH Freer.Pure e h

def eCatch [HasEffect ThrowEff eff] : Elaboration CatchHEff eff := fun op phi next => match op with
    | .Catch => _ >>= next

end Freer
