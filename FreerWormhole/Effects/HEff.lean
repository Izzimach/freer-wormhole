
import FreerWormhole.Effects.Freer

open Freer Effect


--
-- higher-order effects
--

structure HEffect.{u} : Type (u+1) where
    (cmd : Type u)
    (fork : cmd  → Effect.{u})
    (retH : cmd → Type u)

section HEffect

-- Choose one HEffect from a list of them.
inductive HOU.{u} : List HEffect → (ret : Type u) → Effect.{u} → Type (u+1) where
    | Leaf : (c : heff.cmd) → HOU (heff :: heffs) (heff.retH c) (heff.fork c)
    | Node : HOU heffs c fork → HOU (_ :: heffs) c fork


inductive Hefty.{u} : List HEffect.{u} → Type u → Type (u+2) where
| Pure {a : Type u} : a → Hefty h a
| Impure {x : Type u} {e : Effect.{u}} : HOU h x e → ((c : e.op) → Hefty h (e.ret c)) → (x → Hefty h a) → Hefty h a

class HasHEffect (h : HEffect) (heffs : List HEffect) where
    inject : (c : h.cmd) → HOU heffs (h.retH c) (h.fork c)

instance : HasHEffect h (h :: heffs) where
    inject := fun c => @HOU.Leaf h heffs c

instance [HasHEffect h heffs] : HasHEffect h (z :: heffs) where
    inject := fun c => HOU.Node (@HasHEffect.inject h heffs _ c)

def decompHOU {eff : Effect} {heff : HEffect} {heffs : List HEffect} (hou : HOU (heff :: heffs) x eff) : Sum (HOU heffs x eff) heff.cmd :=
    match hou with
    | .Leaf c => Sum.inr c
    | .Node hou' => Sum.inl hou'


def hPure (val : a) : Hefty h a := .Pure val

def hBind (m : Hefty h a) (f : a → Hefty h b) : Hefty h b :=
    match m with
    | .Pure a => f a
    | .Impure ou psi next => .Impure ou psi (fun x => hBind (next x) f)

instance : Monad (Hefty effs) where
    pure := hPure
    bind := hBind





-- an algebra for Hefty h a
def algH.{u} (heffs : List HEffect.{u}) (f : Type u → Type (u+1)) : Type (u+1) :=
    {x a : Type u} → {e : Effect.{u}} → (c : HOU heffs x e) → ((s : e.op) → f ((e.ret s))) → (x → f a) → f a

def cataH.{u} {heffs : List HEffect.{u}} {a : Type u} {f : Type u → Type (u+1)} (pf : {x : Type u} → x → f x) (alg : algH heffs f) (t : Hefty heffs a) : f a :=
    match t with
    | Hefty.Pure x => pf x
    | Hefty.Impure ou psi next => alg ou (fun x => cataH pf alg (psi x)) (fun x => cataH pf alg (next x))


def Elaboration (heffs : List HEffect) (effs : List Effect) : Type (u+1) := algH heffs (Freer effs)

def elaborate (e : Elaboration heffs eff) (h : Hefty heffs a) : Freer eff a := cataH Freer.Pure e h

-- Elaboration eloborations a whole list of HEffects into a Freer of effects.
-- Elab1 adds elaboration for a single HEffect onto an Elaboration. You can use this to build
-- up an Elaboration by chaining of several Elab1 terms.
def Elab1 (heff : HEffect) (heffs : List HEffect) (effs : List Effect) : Type (u+1) := Elaboration heffs effs → Elaboration (heff :: heffs) effs






def NilEffect.{u} : Effect.{u} :=
{
    -- we use Fin 0 as a stand-in for bottom
    op := ULift <| Fin 0,
    ret := fun _ => ULift <| Fin 0
}

def NilHandler : Handler.{u} a a NilEffect effs PUnit :=
    {
        ret := fun a _ => .Pure a,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => Fin.elim0 (ULift.down l)
            | .Node ou' => .Impure ou' (fun x => next x s)
    }





def hLifted (eff : Effect.{u}) : HEffect := 
    {
        cmd := eff.op,
        fork := fun _ => NilEffect.{u},
        retH := eff.ret
    }

def hLift {eff : Effect} [HasHEffect (hLifted eff) heffs] (c : eff.op) : Hefty heffs (eff.ret c) :=
    -- yikes
    @Hefty.Impure heffs _ (eff.ret c) NilEffect (@HasHEffect.inject (hLifted eff) heffs _ c) (fun f0 => Fin.elim0 (ULift.down f0)) hPure


-- a higher-order effect that should not be able to be constructed, used to terminate
-- Heff elaboration
def eNil : Elaboration [hLifted NilEffect] effs :=
    fun c phi next => match c with
                      | .Leaf x => Fin.elim0 (ULift.down x)

def eLift (eff : Effect) [HasEffect eff effs] : Elab1 (hLifted eff) heffs effs :=
    fun elab0 => 
        fun op phi next => match op with
                           | .Leaf c => Freer.Impure (HasEffect.inject c) next
                           | .Node hou' => elab0 hou' phi next



end HEffect