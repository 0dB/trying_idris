module Invoice

-- adding unused constructor to FeeType leads to impossible to understand type errors inside the dependent types instead of
-- just saying that there is a missing case

data FeeType = FeeMarkupHidden | FeeSumItem

-- adding additional constructor to HoursType does _not_ break the code with non-understandable type errors

data HoursType = HoursMarkupHidden | HoursMarkupShown

data BillingItem : Type where
  MkBI : (name : String) -> (quantity : Nat) -> (cents : Nat) -> BillingItem

data BillingHours : Type where
  MkHours : HoursType -> BillingItem -> BillingHours
  NoHours : BillingHours

data Fee : (ft : FeeType) -> Type where
  MkFee : BillingItem -> Fee ft

data ValidArticle : (ft : FeeType) -> Type where
  MkVA : BillingHours ->
         case ft of FeeMarkupHidden => Fee ft; FeeSumItem => Unit;
         ->
         ValidArticle ft

data ValidInvoice : (ft : FeeType) -> Type where
  MkVI : ValidArticle ft ->
         case ft of FeeMarkupHidden => Unit; FeeSumItem => Fee ft;
         ->
         ValidInvoice ft

-- the following type checks, but not if I put -> ValidInvoice1 into each case
-- (I wanted to try out this form to see if it is more readable)
-- but I cannot use ValidInvoice1 and MkVI1 as drop-in replacements for the non-numbered versions!
-- and using proof search yields `bar = MkVI1 (\__pi_arg2 => ())`

-- My best guess so far is that when nested lake t like this the `->` just mean something else (a function type?)

-- I have not been able to construct a value of this type yet. And in the core language representation `ValidArticle` does
-- not even show up. (But OTOH in MkVI `Fee` does not show up either.)

data ValidInvoice1 : (ft : FeeType) -> Type where
  MkVI1 : (case ft of
            FeeMarkupHidden => ValidArticle ft -> Unit
            FeeSumItem      => ValidArticle ft -> Fee ft)
          ->
          ValidInvoice1 ft

-- This type checks, but is there a constructor?
-- in REPL, `ValidInvoice2 FeeSumItem` yields
-- `ValidArticle FeeSumItem      -> Fee FeeSumItem -> ValidInvoice2 FeeSumItem : Type`
-- but `ValidInvoice1 FeeSumItem` yields
-- `ValidInvoice1 FeeSumItem : Type`
-- and proof search fails (because no constructor?)

-- This is sort of how I write it in PureScript (but with a sum type)

ValidInvoice2 : (ft : FeeType) -> Type
ValidInvoice2 FeeMarkupHidden = ValidArticle FeeMarkupHidden -> Unit           -> ValidInvoice2 FeeMarkupHidden
ValidInvoice2 FeeSumItem      = ValidArticle FeeSumItem      -> Fee FeeSumItem -> ValidInvoice2 FeeSumItem

-- this type checks, but what is it?

data VI : Type where
  MkVI2 : ValidInvoice2 ft -> VI

-- this too

data VI20 = MkVI20 (ValidInvoice2 FeeSumItem)

-- this type checks, but what does it _mean_? REPL has same complaint for `MkVI3` as for `MkVI`: Can’t infer argument ft to MkVI
-- so it seems that even for MkVI3 it is clear to the compiler that ft is needed _for MkVI3_. But how to specify it?
-- in the REPL enter MkVI3 {ft = FeeSumItem} to give ft a value

data ValidInvoice3 = MkVI3 (ValidArticle ft) (Fee ft)

-- since this works…

data ValidInvoice4 : (ft : FeeType) -> Type where
  MkVI4 : ValidInvoice4 ft

-- you would think this works

{-
data ValidInvoice5 : (ft : FeeType) -> Type where
  MkVI5 : case ft of
            FeeMarkupHidden => ValidInvoice5 ft
            FeeSumItem      => ValidInvoice5 ft
-}

-- `MkVI6 {ft = FeeMarkupHidden}`
-- how can I add `FeeType` here? In this form of writing a type?

data ValidInvoice6 = MkVI6 (ValidArticle ft) (case ft of FeeMarkupHidden => Unit; FeeSumItem => Fee FeeSumItem)

-- data ValidInvoice7 ft = MkVI7 (ValidArticle ft) (case ft of FeeMarkupHidden => Unit; FeeSumItem => Fee FeeSumItem)

-- Idris handles the dependent types inside MkVI implicitly (MkVA, MkFee)

-- valid in REPL:

{-

MkVI {ft = FeeMarkupHidden} (MkVA (MkHours HoursMarkupShown (MkBI "hours" 2 3)) (MkFee (MkBI "fee hid" 10 200))) ()
MkVI (MkVA (MkHours HoursMarkupShown (MkBI "hours" 2 3))
           (MkFee (MkBI "fee hid" 10 200)))
     () : ValidInvoice FeeMarkupHidden

-}

createInvoiceFeeH : ValidInvoice FeeMarkupHidden
createInvoiceFeeH = MkVI (MkVA (MkHours HoursMarkupShown (MkBI "hours" 2 3)) (MkFee (MkBI "fee hid" 10 200))) ()

createInvoiceFeeS: ValidInvoice FeeSumItem
createInvoiceFeeS = MkVI (MkVA (MkHours HoursMarkupShown (MkBI "hours" 3 4)) ()) (MkFee (MkBI "fee sum" 20 300))

-- Need separate types FeeType and HoursType because of collisions with the dependent types that depend
-- on FeeType.

-- Unit = ()

-- works; this
--     MkVA {ft = FeeMarkupHidden} (MkHours HoursMarkupShown (MkBI "hours" 2 3)) (MkFee (MkBI "fee hid" 10 200))
-- and this
--     the (ValidArticle {ft = FeeMarkupHidden}) (MkVA (MkHours HoursMarkupShown (MkBI "hours" 2 3)) (MkFee (MkBI "fee hid" 10 200)))
-- both yield
--     MkVA (MkHours HoursMarkupShown (MkBI "hours" 2 3))
--          (MkFee (MkBI "fee hid" 10 200)) : ValidArticle FeeMarkupHidden

-- `the (ValidInvoice FeeMarkupHidden) (MkVI (the (ValidArticle FeeMarkupHidden) (MkVA NoHours (the (Fee FeeMarkupHidden) (MkFee)))) ())`
-- yields `MkVI (MkVA NoHours MkFee) ()`
-- this works
-- `the (ValidInvoice FeeMarkupHidden) (MkVI (the (ValidArticle FeeMarkupHidden) (MkVA (MkHours HoursMarkupHidden (MkBI "hours" 2 5)) (the (Fee FeeMarkupHidden) (MkFee)))) ())`
-- but it really only needs a type annotation at the top level:
-- `the (ValidInvoice FeeMarkupHidden) (MkVI (MkVA (MkHours HoursMarkupHidden (MkBI "hours" 2 5)) MkFee) ())`

-- Adding constructors to FeeType leads to type mismatch errors in say MkVI, but they don’t say that
-- there are missing cases, so are hard to interpret

-- the error is
-- Type mismatch between
--   () (Type of ())
-- and
--   case MarkupHidden of
--     MarkupHidden => ()
--     SumItem => Fee SumItem (Expected type)
-- (PureScript handles this the right way and will report missing cases.)
