# idris-lawvre-theories-monad
adapted from: http://gallium.inria.fr/blog/lawvere-theories-and-monads/

todo:

- [ ] Convert this agda to idris

```agda
module Monad where

open import Level

open import Data.Unit hiding (setoid)
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality 
  hiding ( setoid ; isEquivalence )
  renaming ( trans to trans≡ ; sym to sym≡ ; cong to cong≡ ; cong₂ to cong₂≡ ) 

-- Ok, so let's set the scene with some historical context about
-- "computational effects". Back in the days, the only way to describe
-- the semantics of an effectful language was through an "operational
-- semantics": you more or less mimic what the machine does. The lack
-- of compositionality of such model is an annoyance: we would like a
-- "denotational model", in which the denotation of a blurb of code is
-- the composition of the denotation of its pieces.

-- Enters Moggi and his "Notions of Computation and Monads"
-- [http://www.disi.unige.it/person/MoggiE/ftp/ic91.pdf]: by picking
-- a suitable monad, we can interpret our effectful program into an
-- adequate Kleisli category (hence, we get compositionality).

-- From there, Phil Wadler
-- [http://homepages.inf.ed.ac.uk/wadler/papers/essence/essence.ps]
-- brought monads to mainstream programming through Haskell (this is
-- an Agda file: in my frame of reference, Haskell is some sort of
-- COBOL). However, these darned programmers also want to *combine*
-- monads: what if my program is stateful *and* exceptionful: can we
-- automagically build its supporting monad from the State monad and
-- the Exception monad? It's tricky because there can be some funny
-- interaction between State and Exception: upon an exception, do we
-- roll-back the state, or not?

-- In Edinburgh, John Power and Gordon Plotkin realized that (some)
-- monads could be described through a signature -- the effectful
-- operations -- and an equational theory -- describing how these
-- operations interact. As the slogan goes, "notions of computation
-- determine monads"
-- [https://www.era.lib.ed.ac.uk/bitstream/1842/196/1/Comp_Eff_Monads.pdf]:
-- we get the monad from a more basic (and more algebraic, yay!)
-- presentation. Categorically, this combination of a signature and an
-- equational theory is part of the toolbox of "Lawvere theories"
-- [http://ncatlab.org/nlab/show/Lawvere+theory]. I won't go into the
-- categorical details here: Jacques-Henri is holding a gun to my head


-- Before delving into the details, I should hasten to add that these
-- ideas are already percolating into "real-world programming" (again,
-- frame of reference, etc.). Conor McBride and his student Stevan
-- Andjelkovic haven been working on 'Frank'
-- [https://hackage.haskell.org/package/Frank] and its
-- dependently-typed version. Andrej Bauer, Matija Pretnar and their
-- team work on Eff [http://math.andrej.com/eff/], which includes a
-- notion of "effect handler": I'll leave that out completely in this
-- file (but the relationship with delimited continuations is truly
-- fascinating).


-- This file stems from a remark made by Tarmo Uustalu, who told me
-- this "one weird trick" to computing monads. Rumor has it that a
-- similar story is told between the lines in Paul-André Melliès'
-- "Segal condition meets computational effects"
-- [http://www.pps.univ-paris-diderot.fr/~mellies/papers/segal-lics-2010.pdf]
-- but, boy oh boy, there is a lot of space between these lines.


-- * Stateful operations

module StateMonad (S : Set) where

  -- ** Syntax: signature for state

  -- A stateful program is built from two state-manipulating
  -- operations:
  --   * get, which returns the current state
  --   * set, which updates the current state

  -- To formalize this intuition, we write the following signature:

  data ΣState (X : Set) : Set where
    `get : (S → X) → ΣState X
    `set : S × X → ΣState X


  -- Remark: if we were *that* kind of person, we would probably write
  -- ΣState from the following, more elementary blocks:

  data ΣGet (X : Set) : Set where
    `get : (S → X) → ΣGet X
  data ΣSet (X : Set) : Set where
    `set : S × X → ΣSet X
  data _⊕_ (F G : Set → Set)(X : Set) : Set where
    inl : F X → (F ⊕ G) X
    inr : G X → (F ⊕ G) X

  -- which gives: ΣState ≡ ΣGet ⊜ ΣSet

  -- But, for many reasons, this wouldn't be a good idea to follow
  -- that path just now.

  -- ** Free term algebra for State

  -- From a signature, we can build a *syntax* for writing stateful
  -- programs, that is, combining 'get's and 'set's and pure
  -- computations ('return'). Syntax is easy, it's a good ol'
  -- inductive type:

  data StateF (V : Set) : Set where
    return : V → StateF V
    op : ΣState (StateF V) → StateF V

  -- Think of 'V' as a set of variables, then 'StateF V' denotes
  -- stateful computations with variables in 'V'. Unsurprisingly,
  -- 'StateF' is a monad (a rather boring one, but still):

  mutual
    _>>=_ : ∀{V W} → StateF V → (V → StateF W) → StateF W
    return x >>= mf = mf x
    op fa >>= mf = op (ΣStatemap mf fa)
  
    -- Ignore this helper function, it's just here to please the
    -- Termination Checker:
    ΣStatemap : ∀{V W} → (V → StateF W) → ΣState (StateF V) → ΣState (StateF W)
    ΣStatemap mf (`get k) = `get (λ s → (k s) >>= mf)
    ΣStatemap mf (`set (s , k)) = `set (s , k >>= mf)

  -- If one thinks of 'V' and 'W' as sets of variables, then '>>=' can
  -- be thought as implementing a simultaneous substitution. One can
  -- also think of these things as trees (ie. syntax trees) terminated
  -- by 'V' leaves, to which one grafts trees terminated by 'W'
  -- leaves. Whichever you feel comfortable with.

  -- Reassuringly, our 'StateF' monad comes equipped with the
  -- so-called "generic" 'get' and 'set' operations, with the expect
  -- types:

  get : StateF S
  get = op (`get λ s → return s)
  
  set : S → StateF ⊤
  set s = op (`set (s , return tt))

  -- Remark: Yes, yes, there is nothing special about 'StateF': given
  -- any (well-behaved) endofunctor 'F : Set → Set', we could build
  -- another functor 'Free F : Set → Set' which happens to be a monad:
  -- this is the 'free monad' construction
  -- [http://ncatlab.org/nlab/show/free+monad]. We would get, for
  -- free, the substitution '>>='. The free monad construction is a
  -- cottage industry, here are some pointers to the big names on the
  -- market:
  --   * [https://www.fpcomplete.com/user/dolio/many-roads-to-free-monads]
  --   * [http://blog.sigfpe.com/2014/04/the-monad-called-free.html]
  --   * [http://hackage.haskell.org/package/free-operational].

  -- Remark: it is a bit improper to call this thing the 'free monad':
  -- as we shall see, the category terrorist expects some form of quotienting
  -- over that free monad. Here, it is just a lump of syntax: I tend
  -- to call it the 'free term algebra', as in 'it's just syntax'.


  -- At this stage, we can write stateful programs, such as:
       
  test0 : StateF S
  test0 = get >>= λ s → 
          set s >>= λ _ → 
          get >>= λ s' → 
          return s'
  
  test1 : StateF S
  test1 = get >>= λ s' → 
          return  s'
  
  test2 : StateF S
  test2 = get >>= λ s → 
          set s >>= λ _ → 
          return s

  -- ** Equational theory of State
  
  -- Intuitively, the above examples denote the same program. Can we
  -- make this formal?

  -- To do so, we need to equip our syntax with an equational
  -- theory. That is, we need to specify which kind of identities
  -- should hold on stateful programs. Let's see what we want:

  data _≃_ {V : Set} : StateF V → StateF V → Set where

    -- 1. Getting the current state twice is equivalent to getting it
    --    only once
    get-get : ∀{k : S → S → StateF V} → 
            (get >>= (λ s → get >>= λ s' → k s s' )) ≃ (get >>= λ s → k s s )

    -- 2. Setting the state twice is equivalent to performing only the
    --    last 'set'
    set-set : ∀{k s₁ s₂} → 
            (set s₁ >>= (λ _ → set s₂ >>= λ _ → k)) ≃ (set s₂ >>= λ _ → k)

    -- 3. Getting the current state and setting it back in is
    --    equivalent to doing nothing
    get-set : ∀{k} → 
            (get >>= λ s → set s >>= λ _ → k) ≃ k

    -- 4. Setting the state then getting its value is equivalent to
    --    setting the state and directly moving on with that value
    set-get : ∀{k s} → 
            (set s >>= (λ _ → get >>= k)) ≃ (set s >>= λ _ → k s)


  -- Question: Where do these equations come from? Quite frankly, I
  -- took them from Matija Pretnar's thesis
  -- [http://matija.pretnar.info/pdf/the-logic-and-handling-of-algebraic-effects.pdf]. I
  -- hear that Paul-André came up with a minimal set of equations
  -- through some clever trick. There seems to be something 'rewrity'
  -- in the air: how much milliPlotkin would it take to generate these
  -- kinds of "critical pairs"?

  -- Remark: If you're lost and born a mathematician (a dreadful state
  -- of affair), you might want to connect my mumbo-jumbo with the way
  -- one introduces algebraic structures such as monoids, groups,
  -- etc.: 
  --   * One starts by giving a signature of operations, such as
  --     "there is a unary symbol '1' and a binary symbol '.'". That's
  --     a signature, as 'ΣState'.
  --   * Then, one gives a bunch of axioms by equating terms with some
  --     free variables, such as "(a . b) . c = a . (b . c), "e . a =
  --     a". That's an equational theory, as '_≃_' above.


  -- From the theory, we easily build its congruence closure:

  data _∼_ {V : Set} : StateF V → StateF V → Set₁ where
    -- 1. It includes '≃'
    inc : ∀{p q} → p ≃ q → p ∼ q

    -- 2. It is transitive, reflexive, and symmetric
    trans : ∀{p q r} → p ∼ q → q ∼ r → p ∼ r
    refl : ∀{p} → p ∼ p
    sym : ∀{p q} → p ∼ q → q ∼ p

    -- 3. It is a congruence, ie. we can lift it from subterms to
    --    whole terms:
    cong : ∀{W}(tm : StateF W){ps qs : W → StateF V}  → 
           (∀ w → ps w ∼ qs w) → 
           (tm >>= ps) ∼ (tm >>= qs)



  setoid : Set → Setoid _ _
  setoid V = record
    { Carrier       = StateF V
    ; _≈_           = _∼_
    ; isEquivalence = isEquivalence
    }
    where  isEquivalence : ∀ {V : Set} → IsEquivalence (_∼_ {V = V})
           isEquivalence = record
             { refl  = refl
             ; sym   = sym
             ; trans = trans
             }

  --  * Quotient: StateF/∼ = State

  -- What the Lawvere theory tells us is that the Haskellian's state
  -- monad can be recovered from the above, algebraic
  -- presentation. What your local category terrorists would say is
  -- that the Haskellian's state monad is obtained by taking our term
  -- algebra 'StateF' and quotienting it by the congruence
  -- '∼'. However, in type theory (and in programming in general)
  -- quotienting is not an option. Ideally, we would like to find a
  -- definition that is quotiented from the get-go.
  
  -- After thinking very hard, one realizes that every term of
  -- 'StateF' quotiented by '∼' will start with a 'get', followed by a
  -- 'set', followed by a 'return'. We thus have the following normal
  -- form:

  State : Set → Set 
  State X = ΣGet (ΣSet X)

  -- Holy crap, that's the usual State monad! Now, it's time to call
  -- your coworkers: there is some dude on the interwebs that has
  -- found the most convoluted way to build the State monad.


  -- But perhaps you don't trust me when I claim that this is the
  -- normal form. I'm going to (constructively!) prove it to you,
  -- using good ol' normalization by evaluation.

  -- First step, we interpret our stateful terms into a semantic
  -- domain (which is -- extensionally -- quotiented by the theory of
  -- State):

  eval : ∀{A} → StateF A → (S → S × A)
  eval (return a) = λ s → (s , a)
  eval (op (`get k)) = λ s → eval (k s) s
  eval (op (`set (s' , k))) = λ s → eval k s'
  
  -- Second step, we reify the semantic objects into normal forms,
  -- which is trivial:

  reify : ∀{A} → (S → S × A) → State A
  reify {A} f = `get λ s → `set (f s)

  -- The normalization procedure *really* computes the normal form
  norm : ∀{A} → StateF A → State A
  norm p = reify (eval p)

  -- and these normal forms are a subset of terms:
  ⌈_⌉ : ∀{A} → State A → StateF A 
  ⌈ `get k ⌉ = get >>= λ s → help (k s) 
    where help : ∀ {A} → ΣSet A → StateF A
          help (`set (s , v)) = set s >>= λ _ → return v
  

  -- When we read the statement "there exists a normal form"
  -- constructively, it means that we have a procedure that computes
  -- this normal form. That's exactly the 'norm' function.

  -- ** Soundness & Completeness

  -- Now, we want to check that term thus computed is indeed a normal
  -- form. This is captured by two statement, a 'soundness' result and
  -- a 'completeness' result.


  -- (Some auxiliary lemmas, which we prove later:
  pf-sound : ∀{A} → (p : StateF A) → p ∼ ⌈ norm p ⌉
  pf-complete : ∀ {A} {p q : StateF A} → p ∼ q → ∀{s} → eval p s ≡ eval q s
  -- )

  -- First, 'norm' is sound: if two terms have the same normal form,
  -- they belong to the same congruence class:

  sound : ∀ {V} (p q : StateF V) → ⌈ norm p ⌉ ≡ ⌈ norm q ⌉ → p ∼ q
  sound {V} p q r =
    begin
      p
    ≈⟨ pf-sound p ⟩ 
      ⌈ norm p ⌉
    ≡⟨ r ⟩
      ⌈ norm q ⌉
    ≈⟨ sym (pf-sound q) ⟩
      q
    ∎
      where open  import Relation.Binary.EqReasoning (setoid V)
    
  -- Second, 'norm' is complete: if two terms belong to the same
  -- congruence class, they have the same normal form.

  complete : ∀ {A} {p q : StateF A} → p ∼ q → ⌈ norm p ⌉ ≡ ⌈ norm q ⌉
  complete {p = p} {q} r = 
    begin
      ⌈ norm p ⌉
    ≡⟨ refl ⟩
      ⌈ reify (eval p) ⌉
    ≡⟨ cong≡ (λ x → ⌈ reify x ⌉) (ext (λ z → pf-complete r)) ⟩
      ⌈ reify (eval q) ⌉
    ≡⟨ refl ⟩
      ⌈ norm q ⌉
    ∎
    where open ≡-Reasoning

          -- We neeed extensionality, but it's not a big deal: this is a
          -- proof, not a program.
          postulate ext : Extensionality zero zero 


  -- Soundness and completeness rely on these technical lemmas, which
  -- are not worth our attention:
  
  pf-sound (return x) = sym (inc get-set)
  pf-sound {V} (op (`get k)) =
    begin 
      op (`get k)
    ≡⟨ refl ⟩
      get >>= k
    ≈⟨ cong (op (`get return)) 
             (λ s' → pf-sound (k s')) ⟩
       get >>= (λ s' → ⌈ norm (k s') ⌉)
    ≡⟨ refl ⟩
      op (`get λ s' → 
      op (`get (λ s → 
      op (`set (proj₁ (eval (k s') s) , 
      return (proj₂ (eval (k s') s)))))))
    ≈⟨ inc get-get ⟩
      op (`get λ s → 
      op (`set (proj₁ (eval (k s) s) , 
      return (proj₂ (eval (k s) s)))))
    ≡⟨ refl ⟩
      ⌈ norm (op (`get k)) ⌉
    ∎
      where open  import Relation.Binary.EqReasoning (setoid V)
  pf-sound {V} (op (`set (s' , k))) =
    begin 
      op (`set (s' , k ))
    ≈⟨ cong (op (`set (s' , return tt))) (λ _ → pf-sound k) ⟩
      op (`set (s' , ⌈ norm k ⌉) )
    ≡⟨ refl ⟩
      op (`set (s' , 
      op (`get (λ s → 
      op (`set (proj₁ (eval k s),
      return (proj₂ (eval k s))))))))
    ≈⟨ inc set-get ⟩
      op (`set (s' ,
      op (`set (proj₁ (eval k s'),
      return (proj₂ (eval k s'))))))
    ≈⟨ inc set-set ⟩
      op (`set (proj₁ (eval k s'),
      return (proj₂ (eval k s'))))
    ≈⟨ sym (inc get-set) ⟩
      op (`get λ s →
      op (`set (s , 
      op (`set (proj₁ (eval k s'),
      return (proj₂ (eval k s')))))))
    ≈⟨ cong (get >>= return) (λ s → inc set-set) ⟩
      op (`get λ s →
      op (`set (proj₁ (eval k s'),
      return (proj₂ (eval k s')))))
    ≡⟨ refl ⟩
      ⌈ norm (op (`set (s' , k))) ⌉
    ∎
      where open import Relation.Binary.EqReasoning (setoid V)
    
  eval-compose : ∀{A B}(tm : StateF A)(k : A → StateF B){s} → 
               eval (tm >>= k) s
             ≡ (let p : S × A 
                    p = eval tm s in
                 eval (k (proj₂ p)) (proj₁ p))
  eval-compose (return x) k = λ {s} → refl
  eval-compose (op (`get x)) k = λ {s} → eval-compose (x s) k
  eval-compose (op (`set (s' , x))) k = λ {s} → eval-compose x k
    
  pf-complete (inc get-get) = refl
  pf-complete (inc set-set) = refl
  pf-complete (inc set-get) = refl
  pf-complete (inc get-set) = refl
  pf-complete {p = p}{q} (trans {q = r} r₁ r₂) = λ {s} →
    begin 
      eval p s
    ≡⟨ pf-complete r₁ ⟩
      eval r s
    ≡⟨ pf-complete r₂ ⟩
      eval q s
    ∎
    where open ≡-Reasoning
  pf-complete refl = refl
  pf-complete (sym r) = sym≡ (pf-complete r)
  pf-complete (cong tm {ps}{qs} x) = λ {s} → 
    begin
      eval (tm >>= ps) s
    ≡⟨ eval-compose tm ps ⟩
      eval (ps (proj₂ (eval tm s))) (proj₁ (eval tm s))
    ≡⟨ pf-complete (x (proj₂ (eval tm s))) ⟩
      eval (qs (proj₂ (eval tm s))) (proj₁ (eval tm s))
    ≡⟨ sym≡ (eval-compose tm qs) ⟩
      eval (tm >>= qs) s
    ∎
    where open ≡-Reasoning

  -- ** Examples

  -- Right. Now we have a reflexive decision procedure for equality of
  -- stateful programs. Let's use it!

  -- For instance we can "prove" (by a trivial reasoning) that our
  -- earlier programs 'test0', 'test1' and 'test2' are all equivalent:

  test01 : test0 ∼ test1
  test01 = sound test0 test1 refl
  
  test12 : test1 ∼ test2
  test12 = sound test1 test2 refl

  -- The trick here is to rely on the soundness of normalization and
  -- compare the norm forms for equality.


  -- We can also do some funky reasoning. For instance, Gabriel was
  -- wondering why 'cong' is right-leaning: we can only substitute for
  -- subterms 'ps' and 'qs' under a common 'tm', while one might want
  -- to have a more general version:

  cong₂ : ∀{V W}(tm tm' : StateF W){ps qs : W → StateF V}  → 
         (tm ∼ tm') →
         (∀ w → ps w ∼ qs w) → 
         (tm >>= ps) ∼ (tm' >>= qs)

  -- We prove this more general statement by working over the normal
  -- forms. First, a boring, technical lemma that generalizes
  -- 'eval-compose' to the normalization procedure:

  norm-compose : ∀{V W}(tm : StateF W)(ps : W → StateF V) →
    ⌈ norm (tm >>= ps) ⌉ ≡ ⌈ norm (⌈ norm tm ⌉ >>= λ w → ⌈ norm (ps  w) ⌉) ⌉
  norm-compose tm ps = 
    begin
      ⌈ norm (tm >>= ps) ⌉
    ≡⟨ refl ⟩
       op (`get (λ s →
       op (`set (let p : S × _
                     p = eval (tm >>= ps) s in
       proj₁ p , return (proj₂ p)))))
    ≡⟨ cong≡ (λ k → op (`get k)) (ext help) ⟩
       op (`get (λ s →
       (op (`set (let p₁ : S × _
                      p₁ = eval tm s 
                      p₂ : S × _
                      p₂ = eval (ps (proj₂ p₁)) (proj₁ p₁) in
           proj₁ p₂ , return  (proj₂ p₂))))))
    ≡⟨ refl ⟩
      ⌈ norm (⌈ norm tm ⌉ >>= λ w → ⌈ norm (ps  w) ⌉) ⌉
    ∎
      where postulate ext : Extensionality zero zero 
            open ≡-Reasoning
            help : (s : S) → (op (`set (let p : S × _
                                            p = eval (tm >>= ps) s in
                                 proj₁ p , return (proj₂ p))))
                           ≡ (op (`set (let p₁ : S × _
                                            p₁ = eval tm s 
                                            p₂ : S × _
                                            p₂ = eval (ps (proj₂ p₁)) (proj₁ p₁) in
                                 proj₁ p₂ , return  (proj₂ p₂))))
            help s = cong≡ (λ { (s , k) →  op (`set (s , return k)) }) (eval-compose tm ps) 


  -- From which follows the generalized congruence:

  cong₂ {V} tm tm' {ps}{qs} q qp = sound (tm >>= ps) (tm' >>= qs)
    (begin
      ⌈ norm (tm >>= ps) ⌉
    ≡⟨ norm-compose tm ps ⟩
      ⌈ norm (⌈ norm tm ⌉ >>= λ w → ⌈ norm (ps  w) ⌉) ⌉
    -- Remark: we are using the completeness here!
    ≡⟨ cong₂≡ (λ t k → ⌈ norm (t >>= k) ⌉) 
              (complete q) 
              (ext (λ w → complete (qp w))) ⟩
      ⌈ norm (⌈ norm tm' ⌉ >>= λ w → ⌈ norm (qs  w) ⌉) ⌉
    ≡⟨ sym≡ (norm-compose tm' qs) ⟩
      ⌈ norm (tm' >>= qs) ⌉
    ∎)
      where postulate ext : Extensionality zero zero 
            open ≡-Reasoning

  
-- * Tick monad

open import Algebra
import Level

-- I've hinted at the fact that:
--   1. We could generalize much of the above machinery (free monad,
--      congruence, etc.), and
--   2. There is a general principle at play when going from signature
--      & equations to some normal form representation

-- To give another hint, let me breeze through another monad, namely
-- the 'tick' monad.

module Tick (M : Monoid Level.zero Level.zero) where

  open Monoid M

  -- Let 'M' be a monoid. We call 'R' its carrier.

  R : Set
  R = Carrier

  -- ** Signature for counter

  -- The 'Tick' monad has a single operation, 'tick' which lets us add
  -- some amount 'r : R' to a global counter.

  data ΣTick (X : Set) : Set where
    `tick : R × X → ΣTick X

  -- ** Free term algebra

  -- As usual, we get the syntax for tickful programs:

  data TickF (V : Set) : Set where
    return : V → TickF V
    op : ΣTick (TickF V) → TickF V

  tick : R → TickF ⊤
  tick r = op (`tick (r , return tt))

  mutual
    _>>=_ : ∀{A B} → TickF A → (A → TickF B) → TickF B
    return x >>= mf = mf x
    op fa >>= mf = op (ΣTickmap mf fa)

    ΣTickmap : ∀{A B} → (A → TickF B) → ΣTick (TickF A) → ΣTick (TickF B)
    ΣTickmap mf (`tick (r , k)) = `tick (r , k >>= mf)

  -- ** Equational theory

  -- The equational theory, once again stolen from Matija's thesis, is
  -- as follows:

  data _≃_ {V : Set} : TickF V → TickF V → Set where
    -- 1. Counting ε ticks amounts to nothing:
    tick-eps : ∀{k : TickF V} → 
      (tick ε >>= λ _ → k) ≃ k

    -- 2. Counting r₁ ticks followed by r₂ ticks amounts to counting 
    --    r₁ ∙ r₂ ticks:
    tick-com : ∀{k : TickF V}{r₁ r₂} →
      (tick r₁ >>= λ _ → 
       tick r₂ >>= λ _ → k) ≃ (tick (r₁ ∙ r₂) >>= λ _ → k)

  -- ** Normal form

  -- Again, we think very hard and realize that every 'TickF' program
  -- amounts to a single tick (counting the sum of all sub-ticks):
  Tick : Set → Set 
  Tick X = ΣTick X

  -- We "prove" this a posteriori by a NbE procedure:
  eval : ∀{A} → TickF A → R × A
  eval (return a) = ε , a
  eval {A} (op (`tick (r , k))) = 
    let p : R × A 
        p = eval k in
     r ∙ (proj₁ p) , proj₂ p

  reify : ∀{A} → R × A → Tick A
  reify {A} (r , a) = `tick (r , a)

  norm : ∀{A} → TickF A → Tick A
  norm p = reify (eval p)

  ⌈_⌉ : ∀{A} → Tick A → TickF A 
  ⌈ `tick (r , a) ⌉ = tick r >>= λ _ → return a

  -- Gabriel has allowed me to skip the proof: let's hope that it's
  -- indeed true!


-- * Conclusion: 

-- We have recovered the usual State (and Tick) monad from an
-- algebraic presentation based on an equational theory. The key idea
-- was to consider the equational theory as a rewriting system and
-- look for its normal forms. We have justified this equivalence
-- through a normalization-by-evaluation procedure, which we then
-- abused to get proofs by reflection.

-- I wonder how much of all that is already included in Danel Ahman
-- and Sam Staton's "Normalization by Evaluation and Algebraic
-- Effects"
-- [http://homepages.inf.ed.ac.uk/s1225336/papers/mfps13.pdf]: let's
-- push that on my toread list.


-- Exercises:

--   1. Implement a generic "free monad construction", equipped with
--      its operators (return, map, and bind). 

--   2. Recast the State and Tick monads in that mold. 

--   3. Implement another monad in that framework. Careful, you're
--      probably thinking about the Exception monad: handling
--      exceptions is not an algebraic effect, so it won't work. If
--      you restrict yourself to 'throw' (ignoring 'catch'), that
--      should work tho.

-- Open questions: 

--   * I have used intuitions and terminology from rewriting theory to
--     justify my moves: could we further iron out this connection?

--   * Stevan also wonders whether one could relate the duality
--     adjunction/monad to something rewrity? The categorical aspects
--     seem to be nicely presented in "Handling Algebraic Effects"
--     [http://arxiv.org/abs/1312.1399]

--   * I have left aside the question of *combining* theories: what
--     about combining state and tick, etc.? Again, categorically,
--     Plotkin, Power and Hyland have covered a lot of ground in
--     "Combining effects: sum and tensor"
--     [http://homepages.inf.ed.ac.uk/gdp/publications/Comb_Effects_Jour.pdf]. However,
--     Tarmo's talk at IHP seem to suggest that there is more to it
--     than tensor and sums (sorry, I can't find the slides online).

--   * Algebraic effects do not capture all monads: the Exception
--     monad (the one with a 'throw' *and* a 'catch') is such a
--     monad. Does the notion of 'effect handling'/'delimited
--     continuation' fit into the rewriting picture?
```
