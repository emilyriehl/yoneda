/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------


# Basics of Categories
## Sina Hazratpour
## Introduction to Proof  
## MATH 301, Johns Hopkins University, Fall 2022   
-/





/-
 "_Category theory takes a bird’s eye view of mathematics. From high in the sky, details become invisible, but we can spot patterns that were impossible to detect from ground level._" 
-- From "Basic Category Theory" by Tom Leinster
-- 
-/

-- import tactic.rewrite
import tactic.tidy -- for .obviously tactic which we actually do not use in below since explicitly give the proof of natuality conditions, etc.  Feel free to comment this out. 

-- import tactic.find 
import tactic.induction -- for variations on Lean's builtin induction and cases

-- To handle the distinction between small and large categories we need variables for universe levels  (in the order that they were declared).
universes v₁ u₁

/-
A __precategory structure__ consists of

1. a collection of __objects__,
2. a collection of __morphisms__, (maps between objects)
3. a composition operation whereby we can compose morphisms with compatible domain/codomain,
4. an operation which provides identity morphism for each object in the category. 
-/

class precategory (obj : Type u₁) : Type (max u₁ (v₁+1))  :=
(hom : obj → obj → Type v₁) -- for any two objects `X : obj` and `Y : obj` we have the type `hom X Y` of morphisms between `X` and `Y` 
(id       : Π X : obj, hom X X) -- specifies identity morphism for all types 
(comp     : Π {X Y Z : obj}, (hom X Y) → (hom Y Z) → (hom X Z) )


/-! #### notation remarks
There is a special notation for the morphisms in a category: if `X Y : C`, we write

-  `X ⟶ Y` for the type `hom X Y`  of morphisms from `X` to `Y`.  Note: X ⟶ Y is entirely different than the type X → Y of functions from `X` to `Y`.  
(To enter the special arrow `⟶`, type `\h` or `\hom`, or hover over the symbol to see the hint.)

- `𝟙 X` is a the identity morphisms on `X` (i.e., a term of type `X ⟶ X`).  (To enter the special arrow `𝟙`, type `\b1` or hover over the symbol to see the hint.)

- If `f : X ⟶ Y` and `g : Y ⟶ Z`, then we write `g ⊚ f` for the composition, a morphism `X ⟶ Z`. -- this is composition in every category, not necessarily in the category of types
-/

infixr ` ⟶ `:10 := precategory.hom -- type as \h or \hom
notation `𝟙` := precategory.id -- type as \b1
-- infixr ` ⊚ `:80 := precategory.comp-- type as \oo

local notation f ` ⊚ `:80 g:80 := precategory.comp g f    -- type as \oo

/- 
### Extending a Precategory to a Category Structure
- Now, we add the axioms of __unitality__ and __associativity__ to extend the structure of a precategory to a category. 
- The typeclass `category C` describes morphisms associated to objects of type `C`.
-/

class category (obj : Type u₁) extends precategory.{v₁} obj : Type (max u₁ (v₁+1)) :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), f ⊚ (𝟙 X)  = f . obviously) -- naming based diagrammatic order of composition
(comp_id' : ∀ {X Y : obj} (f : hom X Y), (𝟙 Y) ⊚ f = f . obviously)
(comp_assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f) . obviously)

/-
`restate_axiom` is a command that creates a lemma from a structure field discarding any auto_param wrappers from the type.
It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".
-/
restate_axiom category.id_comp'
restate_axiom category.comp_id'
restate_axiom category.comp_assoc'

/-
We add the attributes `simp` so that the tactic `simp` works when using these lemmas to simplify the state of our proofs. 
-/
attribute [simp] category.id_comp category.comp_id category.comp_assoc
-- attribute [trans] precategory.comp

initialize_simps_projections category (to_precategory_hom → hom,
  to_precategory_comp → comp, to_precategory_id → id, -to_precategory)

/-
A `locally_small_category` has objects in one universe level higher than the universe level of the morphisms, e.g. the category of types, or the category of groups, etc.
-/
abbreviation locally_small_category (C : Type (u₁+1)) : Type (u₁+1) := category.{u₁} C
/--
A `small_category` has objects and morphisms in the same universe level.
-/
abbreviation small_category (C : Type u₁) : Type (u₁+1) := category.{u₁} C

namespace category

/-! ### Large Category of Types
There is a large category of types where the objects are types and the morphisms are functions between types. -/
instance cat_of_types : locally_small_category Type* :=
{ 
  hom := λ X, λ Y, X → Y,
  id := λ X, id,
  comp := λ X Y Z, λ f, λ g, g ∘ f,
-- By the tidy tactic, this still typechecks with the remaining lines commented out.
  id_comp' := by {intros X Y, intro f, refl},
  comp_id' := by {intros X Y, intro f, refl},
  comp_assoc' := by {
                      intros W X Y Z, 
                      intros f g h, 
                      refl, 
                    } 
}

/-! ## The Opposite Category 
If `𝓒` is a category, then `𝓒ᵒᵖ` is the __opposite category__, with objects the same but all arrows reversed. `𝓒ᵒᵖ` is the mirror image of `𝓒`. If `X ⟶ Y ⟶ Z` are morphisms in `𝓒ᵒᵖ` then `Z ⟶ Y ⟶ X`  are maps in `𝓒`. 

In below we give `𝓒ᵒᵖ` the structure of a category. See `opposite_cat`. 
-/

variables {𝓒 : Type u₁} [category.{v₁} 𝓒] {W X Y Z : 𝓒} {A : Type}

/- This defines the underlying type of the opposite category. It needs to be different from the underlying type of the category because we defined precategories as type classes. -/
def opposite (𝓒 : Type u₁) : Type u₁ := 𝓒

notation X `ᵒᵖ`:std.prec.max_plus := opposite X

/- The canonical map `𝓒 → 𝓒ᵒᵖ`. 
We need to write `op X` to explicitly move `X` to the opposite category-/
@[pp_nodot]
def op : 𝓒 → 𝓒ᵒᵖ := id 

/- The canonical map `𝓒ᵒᵖ → 𝓒`. -/
@[pp_nodot]
def unop : 𝓒ᵒᵖ → 𝓒 := id

@[simp] 
lemma op_unop (X : 𝓒ᵒᵖ) : op (unop X) = X := rfl
@[simp] 
lemma unop_op (X : 𝓒) : unop (op X) = X := rfl

instance opposite_cat {𝓒 : Type u₁} [category.{v₁} 𝓒] : category.{v₁} 𝓒ᵒᵖ :=
{ 
  hom := λ X, λ Y, (unop Y ⟶ unop X), -- informally, hom_{𝓒ᵒᵖ} X Y = hom_{𝓒} Y X
  id := λ X, 𝟙 (unop X),
  comp := λ X Y Z, λ f g, f ⊚ g,
  id_comp' := by {intros X Y f, simp,},
  comp_id' := by {intros X Y f, simp,},
  comp_assoc' := by {intros _ _ _ _ _ _ _, rw comp_assoc, } 
}

/- API for the opposite category-/

-- The opposite of an arrow in `𝓒`.
def hom.op  {X Y : 𝓒} (f : X ⟶ Y) : 
op Y ⟶ op X 
:= f

-- The opposite of an arrow in `𝓒ᵒᵖ`.
def hom.unop {X Y : 𝓒ᵒᵖ} (f : X ⟶ Y) : 
unop Y ⟶ unop X 
:= f

@[simp] 
lemma op_comp {X Y Z : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} :
  hom.op (g ⊚ f) = hom.op f ⊚ hom.op g := 
begin 
  refl, 
end   

@[simp] 
lemma unop_comp {X Y Z : 𝓒ᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
  hom.unop (g ⊚ f) = hom.unop f ⊚ hom.unop g := 
begin 
  refl, 
end   

@[simp] 
lemma op_id {X : 𝓒} : hom.op (𝟙 X) = 𝟙 (op X) := 
begin
  refl, 
end 

@[simp] 
lemma unop_id {X : 𝓒ᵒᵖ} : hom.unop (𝟙 X) = 𝟙 (unop X) := 
begin
  refl, 
end 

/- `type_equiv` (function equivalence) is the type of functions from `X → Y` with a two-sided inverse -/ 
structure type_equiv (X : Type u₁) (Y : Type u₁) :=
(to_fun    : X → Y)
(inv_fun   : Y → X)
(left_inv  : inv_fun ∘ to_fun = id) -- i.e. inv_fun ∘ to_fun = id_X
(right_inv : to_fun ∘ inv_fun = id) -- i.e. to_fun ∘ inv_fun = id_Y

structure cat_equiv (X Y : 𝓒) :=
(to_mor    : X ⟶ Y)
(inv_mor   : Y ⟶ X)
(left_inv  : to_mor ⊚  inv_mor = (𝟙 Y) ) 
(right_inv : inv_mor ⊚ to_mor = (𝟙 X)  )

infix ` ≅ `:85 := type_equiv
infix ` ≃ `:85 := cat_equiv

set_option trace.simp_lemmas true
/- The equivalence between a type and its opposite. -/
def equiv_to_opposite : 𝓒 ≅ 𝓒ᵒᵖ :=
{ 
  to_fun := op,
  inv_fun := unop,
  left_inv := by {ext, simp,},
  right_inv := by {ext, simp,}, 
} 

def types_equiv_to_opposite : 𝓒 ≃ 𝓒ᵒᵖ := 
{ 
  to_mor := equiv_to_opposite.to_fun,
  inv_mor := equiv_to_opposite.inv_fun,
  left_inv := by {ext, apply op_unop, },
  right_inv := by {ext, apply unop_op}, 
}  

/-! ## Functors
Functors are homomorphism of categories, they are the way we map one category into another. 

A homomorphism `F : 𝓒 → 𝓓` maps 
- the objects of `𝓒` to the objects of `𝓓` (via a function `F₀ : 𝓒.obj → 𝓓.obj`)
- the morphisms of `𝓒` to the morphisms of `𝓓` (via a function `F₁ : 𝓒.mor → 𝓓.mor`)
in such a way that the operations of identity and compositions are preserved, i.e. 
- `F₁ (𝟙 X) = 𝟙 (F₀ X)` --  identities in `𝓒` go to identities in `𝓓` 
- `F₁ (g ⊚ f) = F₁(g) ⊚ F₁(f)` -- compositions in `𝓒` go to compositions in `𝓓` 
-/

universes v₂ v₃ v₄ u₂ u₃ u₄ 

/- There is no canonical instance of a functor between a fixed pair of categories. Thus, we define this as a structure rather than as a type class. -/
@[ext]
structure functor (𝓒 : Type u₁) [category.{v₁} 𝓒] (𝓓 : Type u₂) [category.{v₂} 𝓓] : Type (max v₁ v₂ u₁ u₂) :=
(obj [] : 𝓒 → 𝓓) -- the object function of functor structure
(mor [] : Π {X Y : 𝓒}, (X ⟶ Y) → (obj X ⟶ obj Y)) -- the morphism function of functor structure
(resp_id'   : 
∀ (X : 𝓒), mor (𝟙 X) = 𝟙 (obj X) )
(resp_comp' : 
∀ {X Y Z : 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z), mor (g ⊚ f) = (mor g) ⊚  (mor f) )

infixr ` ⥤ `:26 := functor       -- type as \functor --

restate_axiom functor.resp_id'
attribute [simp] functor.resp_id
restate_axiom functor.resp_comp'
attribute [simp] functor.resp_comp

/- `𝟭 𝓒` is the __identity__ functor on a category `𝓒`. -/
@[simp]
def functor.id (𝓒 : Type u₁) [category.{v₁} 𝓒] : 𝓒 ⥤ 𝓒 :=
{
  obj := id, 
  mor := λ X, λ Y, λ f, f,
  resp_id' := by {intro X, refl, },
  resp_comp' := by {intros X Y Z, intro f, intro g, refl,} 
}

notation `𝟭` := functor.id -- Type this as `\sb1`

variables {𝓓  : Type u₂} [category.{v₂} 𝓓]
          {𝓔 : Type u₃} [category.{v₃} 𝓔]
          {𝓕 : Type u₄} [category.{v₄} 𝓕]

/- We can __compose__ functors. -/
@[simp]
def functor.comp (F : functor 𝓒 𝓓) (G : functor 𝓓 𝓔) : functor 𝓒 𝓔 :=
{
  obj :=  λ X, G.obj (F.obj X), -- G.obj ∘ F.obj, 
  mor := λ X, λ Y, λ f, G.mor (F.mor f), 
  resp_id' := by {intro X, simp only [functor.resp_id ], }, 
  -- simp only improves run time by telling lean what lemmas to use
  resp_comp' := by {intros X Y Z f g, simp only [functor.resp_comp],},  
}

local notation F ` ⊚⊚ `:80 G:80 := functor.comp G F 

/- rewriting along equalities between functors is a bad idea; it leads to lots of complications with heterogenous/dependent equalities, etc. So, we should not add a `simp` tag for the following lemmas. -/ 

lemma functor.id_comp (F : 𝓒 ⥤ 𝓓) : 
  (functor.comp F (𝟭 𝓓))  = F :=
begin
  by cases F; refl,  
end

lemma functor.comp_id (F : 𝓒 ⥤ 𝓓) : 
  (functor.comp F (𝟭 𝓓))  = F :=
begin
  by cases F; refl,  
end

/-! ## The Category of Categories and Functors 
(Small) categories and functors between them form a (locally small) category. To show this, we first need to have a type of all categories and then introduce morphisms (i.e. functors) as part of the would-be structure of a locally small category of categories. 
-/ 

structure Cat := 
(carrier : Type u₁)
(str : small_category carrier)

instance str (𝓒 : Cat) : small_category.{v₁} 𝓒.carrier := 𝓒.str

/-- Category structure on `Cat` -/
instance cat_of_cat : locally_small_category Cat  :=
{ 
  hom := λ 𝓒 𝓓, 𝓒.carrier ⥤ 𝓓.carrier,
  id := λ 𝓒, 𝟭 𝓒.carrier,
  comp := λ 𝓒 𝓓 𝓔 F G, functor.comp F G,  
  id_comp' := by {intros 𝓒 𝓓 F, apply functor.id_comp},
  comp_id' := by {intros 𝓒 𝓓 F, apply functor.id_comp, },
 }

@[simp]
lemma comp_assoc_obj (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) (H : 𝓔 ⥤ 𝓕) 
(X : 𝓒) : 
  ((H ⊚⊚ G) ⊚⊚ F).obj X = (H ⊚⊚ (G ⊚⊚ F)).obj X := 
begin 
  refl, 
end 

@[simp]
lemma comp_assoc_mor (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) (H : 𝓔 ⥤ 𝓕) (X Y: 𝓒) (f : X ⟶ Y): 
  ((H ⊚⊚ G) ⊚⊚ F).mor f = (H ⊚⊚ (G ⊚⊚ F)).mor f := 
begin 
  refl, 
end 

/-! ## Natural transformations

A __natural transformation__ `α : nat_trans F G` consists of morphisms `α.cmpt X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f :  α.cmpt Y ⊚ F.map f = G.map f ⊚ α.cmpt X `, where `f : X ⟶ Y`.

  f : X ----> Y

                  F.mor f
        F.obj X ---------> F.obj Y
          |                  |
          |                  |
α.cmpt X  |                  |α.cmpt Y
          |                  |
          v                  v
        G.obj X ---------> G.obj Y 
                  G.mor f


or even more informally,

      
F X -----> F Y 
 |         |              
 |         |        
 v         v                
G X ----> G Y 
-/

/- The ext tag makes natural transformations satisfy extensionality: to prove two such are equal one gives a componentwise equality. -/
@[ext]
structure nat_trans (F G : 𝓒 ⥤ 𝓓) : Type (max u₁ v₂) :=
(cmpt : Π X : 𝓒, F.obj X ⟶ G.obj X) -- "cmpt" short for "component"
(naturality' : ∀ ⦃X Y : 𝓒⦄ (f : X ⟶ Y), cmpt Y ⊚ (F.mor f) = (G.mor f)  ⊚ cmpt X . obviously) -- the naturality condition

restate_axiom nat_trans.naturality'

/-
Note that we make `nat_trans.naturality` a simp lemma, with the preferred simp normal form pushing the components of natural transformations to the left.
-/ 
attribute [simp] nat_trans.naturality

namespace nat_trans

/- If two natural transforamtions are equal then all of their components are equal. -/

lemma congr_cmpt {F G : 𝓒 ⥤ 𝓓} {α β : nat_trans F G} (h : α = β) (X : 𝓒) : 
  α.cmpt X = β.cmpt X :=
begin
 have h₁ :  α.cmpt = β.cmpt , from congr_arg nat_trans.cmpt h, 
 apply congr_fun h₁, 
end 

/- The __identity__ natural transformation on a functor `
`F`. -/ 

def id (F : 𝓒 ⥤ 𝓓) : nat_trans F F :=
{ 
  cmpt := λ X, 𝟙 (F.obj X), 
  naturality' := by {
                      intros X Y f,
                      simp only [id_comp, comp_id],
                    },  
}

@[simp] 
lemma id_cmpt {F: 𝓒 ⥤ 𝓓} (X : 𝓒) : 
  (nat_trans.id F).cmpt X = 𝟙 (F.obj X) := 
begin
  refl, 
end 

/-! ### Composition of Natural Transformations 

Natural transformations have two kinds of compositions: 

1. The __vertical__ composition, and 
2. The __horizontal__ composition. 

Only vertical composition is used here. -/

/-! #### Vertical Composition of Natural Transformations 

Given functors `F G : 𝓒 ⥤ 𝓓` and natural transformations 
`α : nat_trans F G ` and  `β : nat_trans G H`, for any object `X` in category `𝓒` we obtain the comutative diagram 

F X ----> F Y 
 |         |              
 |         |        
 v         v                
G X ----> G Y 
 |         |
 |         |   
 v         v
H X ----> H Y 

The vertical composition of `α` and `β` has at its `X` components the composite morphism `(β.cmpt X) ⊚ (α.cmpt X)`.   
-/

/-- `vcomp α β` is the __vertical__ compositions of natural transformations. -/

variables {F G H : 𝓒 ⥤ 𝓓}

@[simp]
def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
{ 
  cmpt := λ X, (β.cmpt X) ⊚ (α.cmpt X), 
  naturality' := by { intros X Y f, 
                      rw category.comp_assoc,
                      simp only [α.naturality], 
                      rw ← category.comp_assoc, 
                      simp only [β.naturality], 
                      rw category.comp_assoc,
                      } ,
}

--@[simp]
lemma vcomp_cmpt (α : nat_trans F G) (β : nat_trans G H) (X : 𝓒) :
  (vcomp α β).cmpt X = (β.cmpt X) ⊚ (α.cmpt X)  := 
begin
  refl,
end   

/-
For categories `𝓒 𝓓` we construct a category structures on functors `𝓒 ⥤ 𝓓` using the vertical composition of natural transformations. We call this the __functor category__ of `𝓒` and `𝓓`. 

`functor.cat 𝓒 𝓓` gives the category structure on functors and natural transformations
between categories `𝓒` and `D`.

Notice that if `𝓒` and `𝓓` are both small categories at the same universe level, this is another small category at that level.

However if `𝓒` and `𝓓` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

instance functor.cat : category.{(max u₁ v₂)} (𝓒 ⥤ 𝓓) :=
{ 
  hom     := λ F G, nat_trans F G,
  id      := λ F, nat_trans.id F,
  comp    := λ _ _ _ α β, vcomp α β, 
  id_comp' := by {intros F G θ, ext, simp, },  
  comp_id' := by {intros F G θ, ext, simp, }, 
  comp_assoc' := by {intros F G H K α β γ, ext, simp only [vcomp_cmpt], rw [comp_assoc], },
}

end nat_trans

/-! ### Representable Functors  
To every object `X` of a category `𝓒` we can associate a functor `Ϳ X : 𝓒 ⥤ Type*` which maps an object `Y` in `𝓒` to the hom-type `X ⟶ Y`. 
-/ 

--set_option trace.simp_lemmas true
@[simp]
def functor.representable {𝓒 : Type u₁}[category.{v₁} 𝓒] (X : 𝓒) : 𝓒 ⥤ Type* :=
{ 
  obj := λ Y, X ⟶ Y,
  mor := λ Y Z f g, f ⊚ g,
  resp_id' := by {intro Y, funext, simp, refl, },
  resp_comp' := by {intros X Y Z f g, funext, simp, refl}, 
}

local notation ` 𝕁 ` : 15 :=  functor.representable 

@[simp]
def functor.corepresentable {𝓒 : Type u₁}[category.{v₁} 𝓒] (X : 𝓒) : 𝓒ᵒᵖ ⥤ Type* :=
{ 
  obj := λ Y, unop Y ⟶ X, --  𝓒-morphisms from `Y` to `X`
  mor := λ Y Z f (g : Y ⟶ X), g ⊚ (hom.unop f),
  resp_id' := by {intro Y, funext, simp only [unop_id], simp, refl,  },
  resp_comp' := by {intros U' V' W' f g, simp only [unop_comp], funext x, rw ← comp_assoc, refl, },
}  

local notation ` 𝕐 ` : 15 :=  functor.corepresentable 

@[simp]
lemma rep_obj (A : 𝓒) (B : 𝓒) :  
  (𝕁 A).obj B =  (A ⟶ B) := 
begin
  refl, 
end 

@[simp]
lemma rep_mor (A : 𝓒) {B C : 𝓒} (g : B ⟶ C)  :  
   (𝕁 A).mor g = λ f,  g ⊚ f := 
begin
  refl, 
end

@[simp]
lemma rep_mor_ptwise (A : 𝓒) {B C : 𝓒} (g : B ⟶ C) 
(f : (𝕁 A).obj B) :  
   (𝕁 A).mor g f =  g ⊚ f := 
begin
  refl, 
end

@[simp]
lemma corep_obj (A : 𝓒) (B : 𝓒ᵒᵖ) :  
  (𝕐 A).obj B =  (unop B ⟶ A) := 
begin
  refl, 
end 

@[simp]
lemma corep_mor (A : 𝓒) (B C : 𝓒ᵒᵖ) (f : B ⟶ C) :  
   (𝕐 A).mor f =  λ g, g ⊚ (hom.unop f) := 
begin
  refl, 
end 

lemma cov_naturality.fibrewise {𝓒 : Type*} [category 𝓒] {F : 𝓒 ⥤ Type* } (A : 𝓒) (θ : 𝕁 A ⟶  F) (X : 𝓒)  (f : A ⟶ X) : 
  (θ.cmpt X) f  = (F.mor f) (θ.cmpt A (𝟙 A)) := 
begin
  have this : (θ.cmpt X) f = (θ.cmpt X) (f ⊚ 𝟙 A), by {simp}, 
  rw this,
  rw ← (rep_mor_ptwise A f), 
  conv 
    begin
    to_lhs, 
    change ((θ.cmpt X) ⊚ (𝕁 A).mor f) (𝟙 A)
    end,  
  rw [nat_trans.naturality],    
  refl, 
end 

def yoneda_covariant {𝓒 : Type*} [category 𝓒] {F : 𝓒 ⥤ Type* } (A B : 𝓒) : 
  (𝕁 A ⟶ F) ≅ F.obj A :=
{ to_fun := λ α, α.cmpt A (𝟙 A),
  inv_fun := λ u, { cmpt := λ X, λ f, (F.mor f) u,
                    naturality' := 
                    by { 
                          intros X Y k, 
                          funext f,
                          simp [rep_obj, rep_mor],
                          dsimp, 
                          conv 
                            begin 
                              to_lhs, 
                              change (F.mor (k ⊚ f)) u, 
                            end, 
                          conv 
                            begin
                              to_rhs,
                              change (F.mor k) (F.mor f  u), 
                            end,   
                          rw [functor.resp_comp], 
                          refl,  
                       }, 
                  },
  left_inv :=  by { funext α, dsimp, ext X f, simp, rw ← cov_naturality.fibrewise },
  right_inv := by {funext, dsimp, rw functor.resp_id, refl}, }

end category