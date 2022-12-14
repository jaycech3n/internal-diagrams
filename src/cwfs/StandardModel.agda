{-# OPTIONS --without-K --rewriting #-}

module cwfs.StandardModel where

open import cwfs.CwFs

ð¯ : WildCategory _ _
WildCategory.Ob ð¯ = Typeâ
WildCategoryStructure.wildsemicatstr (WildCategory.wildcatstr ð¯) = record
  { hom = Î» A B â A â B
  ; _â¦_ = Î» g f a â g (f a)
  ; ass = idp }
WildCategoryStructure.id (WildCategory.wildcatstr ð¯) {A} = idf A
WildCategoryStructure.idl (WildCategory.wildcatstr ð¯) = idp
WildCategoryStructure.idr (WildCategory.wildcatstr ð¯) = idp

ð¯-ctxstr : ContextStructure ð¯
ContextStructure.â ð¯-ctxstr = â¤
ContextStructure.â-terminal ð¯-ctxstr A = Î -level Î» _ â Unit-level

ð¯-tytmstr : TyTmStructure ð¯
ð¯-tytmstr = record
  { ctxstr = ð¯-ctxstr
  ; Ty = Î» A â A â Typeâ
  ; _[_] = Î» {A} {B} P f â P â f
  ; [id] = idp
  ; [â¦] = idp
  ; Tm = Î» {A} P â (a : A) â P a
  ; _[_]â = Î» {A} {B} {P} g f â g â f
  ; [id]â = idp
  ; [â¦]â = idp }

ð° : CwFStructure ð¯
CwFStructure.compstr ð° = record
  { tytmstr = ð¯-tytmstr
  ; _â·_ = Î» A P â Î£ A P
  ; Ï = Î» _ â fst
  ; Ï = Î» _ â snd
  ; _,,_ = Î» {A} {B} {P} f g a â f a , g a
  ; Î²Ï = idp
  ; Î²Ï = idp
  ; Î·,, = idp
  ; ,,-â¦ = idp }
