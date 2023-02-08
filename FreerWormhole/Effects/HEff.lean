
import FreerWormhole.Effects.Freer

open Freer Effect


--
-- higher-order effects
--

structure HEffect : Type 2 where
    (cmd : Type 1)
    (fork : cmd  → Effect)
    (retH : cmd → Type)

namespace HEffect

-- Choose one HEffect from a list of them.
inductive HOU : List HEffect → (ret : Type) → Effect → Type 2 where
    | Leaf : (c : heff.cmd) → HOU (heff :: heffs) (heff.retH c) (heff.fork c)
    | Node : HOU heffs c f → HOU (_ :: heffs) c f


inductive Hefty : List HEffect → Type → Type 2 where
    | Pure {a : Type} : a → Hefty h a
    | Impure {a x : Type} {e : Effect} {h : List HEffect} : HOU h x e → ((c : e.op) → Hefty h (e.ret c)) → (x → Hefty h a) → Hefty h a

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

def hSend {heffs : List HEffect} {heff : HEffect} [HasHEffect heff heffs] 
      (c : heff.cmd)
      (hfork : (x : Effect.op (HEffect.fork heff c)) → Hefty heffs (Effect.ret (HEffect.fork heff c) x))
      : Hefty heffs (heff.retH c) :=
    Hefty.Impure
        (@HasHEffect.inject heff heffs _ c)
        hfork
        (fun z => Hefty.Pure z)




-- an algebra for Hefty h a
def algH (heffs : List HEffect) (f : Type → Type 2) : Type 2 :=
    {x : Type} → {a : Type} → {e : Effect} → (c : HOU heffs x e) → ((s : e.op) → f ((e.ret s))) → (x → f a) → f a

def cataH {heffs : List HEffect} {a : Type} {f : Type → Type 2} (pf : {x : Type} → x → f x) (alg : algH heffs f) (t : Hefty heffs a) : f a :=
    match t with
    | Hefty.Pure x => pf x
    | Hefty.Impure ou psi next => alg ou (fun x => cataH pf alg (psi x)) (fun x => cataH pf alg (next x))


def Elaboration (heffs : List HEffect) (effs : List Effect) : Type 2 := algH heffs (Freer effs)

def elaborate (e : Elaboration heffs eff) (h : Hefty heffs a) : Freer eff a := cataH Freer.Pure e h

-- Elaboration eloborations a whole list of HEffects into a Freer of effects.
-- Elab1 adds elaboration for a single HEffect onto an Elaboration. You can use this to build
-- up an Elaboration by chaining of several Elab1 terms.
def Elab1 (heff : HEffect) (heffs : List HEffect) (effs : List Effect) : Type 2 :=
    Elaboration heffs effs → Elaboration (heff :: heffs) effs


-- Elaborations are usually specified as cons-ing an HEffect onto an already-established list of HEffects.
-- To terminate this list of HEffect we use the NilEffect, which elaborates into an 
def NilEffect : Effect :=
    {
        -- we use Fin 0 as a stand-in for bottom
        op := ULift <| Fin 0,
        ret := fun _ => ULift <| Fin 0
    }

def NilHandler : Handler a a NilEffect effs Unit :=
    {
        ret := fun a _ => .Pure a,
        handle := fun ou next s =>
            match ou with
            | .Leaf l => Fin.elim0 (ULift.down l)
            | .Node ou' => .Impure ou' (fun x => next x s)
    }

def hLifted (eff : Effect) : HEffect := 
    {
        cmd := eff.op,
        fork := fun _ => NilEffect,
        retH := eff.ret
    }

def hLift {eff : Effect} {heffs : List HEffect} [HasHEffect (hLifted eff) heffs] (c : eff.op) : Hefty heffs (eff.ret c) :=
    -- yikes
    @Hefty.Impure _ (eff.ret c) NilEffect heffs (@HasHEffect.inject (hLifted eff) heffs _ c) (fun f0 => Fin.elim0 (ULift.down f0)) hPure



def elabEff (eff : Effect) [HasEffect eff effs] : Elab1 (hLifted eff) heffs effs :=
    fun elab0 => 
        fun op phi next => match op with
                           | .Leaf c => Freer.Impure (HasEffect.inject c) next
                           | .Node hou' => elab0 hou' phi next

-- When you use elabEff it works like List.cons, prepending an elaboration onto a list of elaborations.
-- At the end you need elabLast, which is sort of a List.nil for elaboration lists.
def elabLast (eff : Effect) [HasEffect eff effs] : Elaboration [hLifted eff] effs :=
    fun op phi next => match op with
                       | .Leaf c => Freer.Impure (HasEffect.inject c) next

-- a higher-order effect that should not be able to be constructed, used to terminate
-- Heff elaboration
def elabNil : Elaboration [hLifted NilEffect] [] :=
    fun c phi next => match c with
                      | .Leaf x => Fin.elim0 (ULift.down x)


end HEffect
