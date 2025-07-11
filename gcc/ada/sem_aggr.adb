------------------------------------------------------------------------------
--                                                                          --
--                         GNAT COMPILER COMPONENTS                         --
--                                                                          --
--                             S E M _ A G G R                              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 1992-2025, Free Software Foundation, Inc.         --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Aspects;        use Aspects;
with Atree;          use Atree;
with Checks;         use Checks;
with Einfo;          use Einfo;
with Einfo.Utils;    use Einfo.Utils;
with Elists;         use Elists;
with Errid;          use Errid;
with Errout;         use Errout;
with Expander;       use Expander;
with Exp_Tss;        use Exp_Tss;
with Exp_Util;       use Exp_Util;
with Freeze;         use Freeze;
with Itypes;         use Itypes;
with Lib;            use Lib;
with Lib.Xref;       use Lib.Xref;
with Mutably_Tagged; use Mutably_Tagged;
with Namet;          use Namet;
with Namet.Sp;       use Namet.Sp;
with Nmake;          use Nmake;
with Nlists;         use Nlists;
with Opt;            use Opt;
with Restrict;       use Restrict;
with Rident;         use Rident;
with Sem;            use Sem;
with Sem_Aux;        use Sem_Aux;
with Sem_Case;       use Sem_Case;
with Sem_Cat;        use Sem_Cat;
with Sem_Ch3;        use Sem_Ch3;
with Sem_Ch8;        use Sem_Ch8;
with Sem_Ch13;       use Sem_Ch13;
with Sem_Dim;        use Sem_Dim;
with Sem_Eval;       use Sem_Eval;
with Sem_Res;        use Sem_Res;
with Sem_Util;       use Sem_Util;
with Sem_Type;       use Sem_Type;
with Sem_Warn;       use Sem_Warn;
with Sinfo;          use Sinfo;
with Sinfo.Utils;    use Sinfo.Utils;
with Snames;         use Snames;
with Stringt;        use Stringt;
with Stand;          use Stand;
with Style;          use Style;
with Targparm;       use Targparm;
with Tbuild;         use Tbuild;
with Ttypes;         use Ttypes;
with Uintp;          use Uintp;
with Warnsw;         use Warnsw;

package body Sem_Aggr is

   type Case_Bounds is record
      Lo : Node_Id;
      --  Low bound of choice. Once we sort the Case_Table, then entries
      --  will be in order of ascending Choice_Lo values.

      Hi : Node_Id;
      --  High Bound of choice. The sort does not pay any attention to the
      --  high bound, so choices 1 .. 4 and 1 .. 5 could be in either order.

      Highest : Uint;
      --  If there are duplicates or missing entries, then in the sorted
      --  table, this records the highest value among Choice_Hi values
      --  seen so far, including this entry.

      Choice : Node_Id;
      --  The node of the choice
   end record;

   type Case_Table_Type is array (Pos range <>) of Case_Bounds;
   --  Table type used by Check_Case_Choices procedure

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Sort_Case_Table (Case_Table : in out Case_Table_Type);
   --  Sort the Case Table using the Lower Bound of each Choice as the key. A
   --  simple insertion sort is used since the choices in a case statement will
   --  usually be in near sorted order.

   function Cannot_Compute_High_Bound (Index : Entity_Id) return Boolean;
   --  Determines if the type of the given array aggregate index is a modular
   --  type or an enumeration type that will raise CE at runtime when computing
   --  the high bound of a null aggregate.

   procedure Check_Can_Never_Be_Null (Typ : Entity_Id; Expr : Node_Id);
   --  Ada 2005 (AI-231): Check bad usage of null for a component for which
   --  null exclusion (NOT NULL) is specified. Typ can be an E_Array_Type for
   --  the array case (the component type of the array will be used) or an
   --  E_Component/E_Discriminant entity in the record case, in which case the
   --  type of the component will be used for the test. If Typ is any other
   --  kind of entity, the call is ignored. Expr is the component node in the
   --  aggregate which is known to have a null value. A warning message will be
   --  issued if the component is null excluding.
   --
   --  It would be better to pass the proper type for Typ ???

   procedure Check_Expr_OK_In_Limited_Aggregate (Expr : Node_Id);
   --  Check that Expr is either not limited or else is one of the cases of
   --  expressions allowed for a limited component association (namely, an
   --  aggregate, function call, or <> notation). Report error for violations.
   --  Expression is also OK in an instance or inlining context, because we
   --  have already preanalyzed and it is known to be type correct.

   procedure Report_Null_Array_Constraint_Error
     (N         : Node_Id;
      Index_Typ : Entity_Id);
   --  N is a null array aggregate indexed by the given enumeration type or
   --  modular type. Report a warning notifying that CE will be raised at
   --  runtime. Under SPARK mode an error is reported instead of a warning.

   ------------------------------------------------------
   -- Subprograms used for RECORD AGGREGATE Processing --
   ------------------------------------------------------

   procedure Resolve_Record_Aggregate (N : Node_Id; Typ : Entity_Id);
   --  This procedure performs all the semantic checks required for record
   --  aggregates. Note that for aggregates analysis and resolution go
   --  hand in hand. Aggregate analysis has been delayed up to here and
   --  it is done while resolving the aggregate.
   --
   --    N is the N_Aggregate node.
   --    Typ is the record type for the aggregate resolution
   --
   --  While performing the semantic checks, this procedure builds a new
   --  Component_Association_List where each record field appears alone in a
   --  Component_Choice_List along with its corresponding expression. The
   --  record fields in the Component_Association_List appear in the same order
   --  in which they appear in the record type Typ.
   --
   --  Once this new Component_Association_List is built and all the semantic
   --  checks performed, the original aggregate subtree is replaced with the
   --  new named record aggregate just built. This new record aggregate has no
   --  positional associations, so its Expressions field is set to No_List.
   --  Note that subtree substitution is performed with Rewrite so as to be
   --  able to retrieve the original aggregate.
   --
   --  The aggregate subtree manipulation performed by Resolve_Record_Aggregate
   --  yields the aggregate format expected by Gigi. Typically, this kind of
   --  tree manipulations are done in the expander. However, because the
   --  semantic checks that need to be performed on record aggregates really go
   --  hand in hand with the record aggregate normalization, the aggregate
   --  subtree transformation is performed during resolution rather than
   --  expansion. Had we decided otherwise we would have had to duplicate most
   --  of the code in the expansion procedure Expand_Record_Aggregate. Note,
   --  however, that all the expansion concerning aggregates for tagged records
   --  is done in Expand_Record_Aggregate.
   --
   --  The algorithm of Resolve_Record_Aggregate proceeds as follows:
   --
   --  1. Make sure that the record type against which the record aggregate
   --     has to be resolved is not abstract. Furthermore if the type is a
   --     null aggregate make sure the input aggregate N is also null.
   --
   --  2. Verify that the structure of the aggregate is that of a record
   --     aggregate. Specifically, look for component associations and ensure
   --     that each choice list only has identifiers or the N_Others_Choice
   --     node. Also make sure that if present, the N_Others_Choice occurs
   --     last and by itself.
   --
   --  3. If Typ contains discriminants, the values for each discriminant is
   --     looked for. If the record type Typ has variants, we check that the
   --     expressions corresponding to each discriminant ruling the (possibly
   --     nested) variant parts of Typ, are static. This allows us to determine
   --     the variant parts to which the rest of the aggregate must conform.
   --     The names of discriminants with their values are saved in a new
   --     association list, New_Assoc_List which is later augmented with the
   --     names and values of the remaining components in the record type.
   --
   --     During this phase we also make sure that every discriminant is
   --     assigned exactly one value. Note that when several values for a given
   --     discriminant are found, semantic processing continues looking for
   --     further errors. In this case it's the first discriminant value found
   --     which we will be recorded.
   --
   --     IMPORTANT NOTE: For derived tagged types this procedure expects
   --     First_Discriminant and Next_Discriminant to give the correct list
   --     of discriminants, in the correct order.
   --
   --  4. After all the discriminant values have been gathered, we can set the
   --     Etype of the record aggregate. If Typ contains no discriminants this
   --     is straightforward: the Etype of N is just Typ, otherwise a new
   --     implicit constrained subtype of Typ is built to be the Etype of N.
   --
   --  5. Gather the remaining record components according to the discriminant
   --     values. This involves recursively traversing the record type
   --     structure to see what variants are selected by the given discriminant
   --     values. This processing is a little more convoluted if Typ is a
   --     derived tagged types since we need to retrieve the record structure
   --     of all the ancestors of Typ.
   --
   --  6. After gathering the record components we look for their values in the
   --     record aggregate and emit appropriate error messages should we not
   --     find such values or should they be duplicated.
   --
   --  7. We then make sure no illegal component names appear in the record
   --     aggregate and make sure that the type of the record components
   --     appearing in a same choice list is the same. Finally we ensure that
   --     the others choice, if present, is used to provide the value of at
   --     least a record component.
   --
   --  8. The original aggregate node is replaced with the new named aggregate
   --     built in steps 3 through 6, as explained earlier.
   --
   --  Given the complexity of record aggregate resolution, the primary goal of
   --  this routine is clarity and simplicity rather than execution and storage
   --  efficiency. If there are only positional components in the aggregate the
   --  running time is linear. If there are associations the running time is
   --  still linear as long as the order of the associations is not too far off
   --  the order of the components in the record type. If this is not the case
   --  the running time is at worst quadratic in the size of the association
   --  list.

   procedure Check_Misspelled_Component
     (Elements  : Elist_Id;
      Component : Node_Id);
   --  Give possible misspelling diagnostic if Component is likely to be a
   --  misspelling of one of the components of the Assoc_List. This is called
   --  by Resolve_Aggr_Expr after producing an invalid component error message.

   -----------------------------------------------------
   -- Subprograms used for ARRAY AGGREGATE Processing --
   -----------------------------------------------------

   function Resolve_Array_Aggregate
     (N              : Node_Id;
      Index          : Node_Id;
      Index_Constr   : Node_Id;
      Component_Typ  : Entity_Id;
      Iterated       : Boolean;
      Others_Allowed : Boolean) return Boolean;
   --  This procedure performs the semantic checks for an array aggregate.
   --  True is returned if the aggregate resolution succeeds.
   --
   --  The procedure works by recursively checking each nested aggregate.
   --  Specifically, after checking a sub-aggregate nested at the i-th level
   --  we recursively check all the subaggregates at the i+1-st level (if any).
   --  Note that aggregates analysis and resolution go hand in hand.
   --  Aggregate analysis has been delayed up to here and it is done while
   --  resolving the aggregate.
   --
   --    N is the current N_Aggregate node to be checked.
   --
   --    Index is the index node corresponding to the array sub-aggregate that
   --    we are currently checking (RM 4.3.3 (8)). Its Etype is the
   --    corresponding index type (or subtype).
   --
   --    Index_Constr is the node giving the applicable index constraint if
   --    any (RM 4.3.3 (10)). It "is a constraint provided by certain
   --    contexts [...] that can be used to determine the bounds of the array
   --    value specified by the aggregate". If Others_Allowed below is False
   --    there is no applicable index constraint and this node is set to Index.
   --
   --    Component_Typ is the array component type.
   --
   --    Iterated indicates whether the aggregate appears in the context of an
   --    iterated association for a parent aggregate.
   --
   --    Others_Allowed indicates whether an others choice is allowed
   --    in the context where the top-level aggregate appeared.
   --
   --  The algorithm of Resolve_Array_Aggregate proceeds as follows:
   --
   --  1. Make sure that the others choice, if present, is by itself and
   --     appears last in the sub-aggregate. Check that we do not have
   --     positional and named components in the array sub-aggregate (unless
   --     the named association is an others choice). Finally if an others
   --     choice is present, make sure it is allowed in the aggregate context.
   --
   --  2. If the array sub-aggregate contains discrete_choices:
   --
   --     (A) Verify their validity. Specifically verify that:
   --
   --        (a) If a null range is present it must be the only possible
   --            choice in the array aggregate.
   --
   --        (b) Ditto for a non static range.
   --
   --        (c) Ditto for a non static expression.
   --
   --        In addition this step analyzes and resolves each discrete_choice,
   --        making sure that its type is the type of the corresponding Index.
   --        If we are not at the lowest array aggregate level (in the case of
   --        multidimensional aggregates) then invoke Resolve_Array_Aggregate
   --        recursively on each component expression. Otherwise, resolve the
   --        bottom level component expressions against the expected component
   --        type ONLY IF the component corresponds to a single discrete choice
   --        which is not an others choice (to see why read the DELAYED
   --        COMPONENT RESOLUTION below).
   --
   --     (B) Determine the bounds of the sub-aggregate and lowest and
   --         highest choice values.
   --
   --  3. For positional aggregates:
   --
   --     (A) Loop over the component expressions either recursively invoking
   --         Resolve_Array_Aggregate on each of these for multidimensional
   --         array aggregates or resolving the bottom level component
   --         expressions against the expected component type.
   --
   --     (B) Determine the bounds of the positional sub-aggregates.
   --
   --  4. Try to determine statically whether the evaluation of the array
   --     sub-aggregate raises Constraint_Error. If yes emit proper
   --     warnings. The precise checks are the following:
   --
   --     (A) Check that the index range defined by aggregate bounds is
   --         compatible with corresponding index subtype.
   --         We also check against the base type. In fact it could be that
   --         Low/High bounds of the base type are static whereas those of
   --         the index subtype are not. Thus if we can statically catch
   --         a problem with respect to the base type we are guaranteed
   --         that the same problem will arise with the index subtype
   --
   --     (B) If we are dealing with a named aggregate containing an others
   --         choice and at least one discrete choice then make sure the range
   --         specified by the discrete choices does not overflow the
   --         aggregate bounds. We also check against the index type and base
   --         type bounds for the same reasons given in (A).
   --
   --     (C) If we are dealing with a positional aggregate with an others
   --         choice make sure the number of positional elements specified
   --         does not overflow the aggregate bounds. We also check against
   --         the index type and base type bounds as mentioned in (A).
   --
   --     Finally construct an N_Range node giving the sub-aggregate bounds.
   --     Set the Aggregate_Bounds field of the sub-aggregate to be this
   --     N_Range. The routine Array_Aggr_Subtype below uses such N_Ranges
   --     to build the appropriate aggregate subtype. Aggregate_Bounds
   --     information is needed during expansion.
   --
   --  DELAYED COMPONENT RESOLUTION: The resolution of bottom level component
   --  expressions in an array aggregate may call Duplicate_Subexpr or some
   --  other routine that inserts code just outside the outermost aggregate.
   --  If the array aggregate contains discrete choices or an others choice,
   --  this may be wrong. Consider for instance the following example.
   --
   --    type Rec is record
   --       V : Integer := 0;
   --    end record;
   --
   --    type Acc_Rec is access Rec;
   --    Arr : array (1..3) of Acc_Rec := (1 .. 3 => new Rec);
   --
   --  Then the transformation of "new Rec" that occurs during resolution
   --  entails the following code modifications
   --
   --    P7b : constant Acc_Rec := new Rec;
   --    RecIP (P7b.all);
   --    Arr : array (1..3) of Acc_Rec := (1 .. 3 => P7b);
   --
   --  This code transformation is clearly wrong, since we need to call
   --  "new Rec" for each of the 3 array elements. To avoid this problem we
   --  delay resolution of the components of non positional array aggregates
   --  to the expansion phase. As an optimization, if the discrete choice
   --  specifies a single value we do not delay resolution.

   function Array_Aggr_Subtype (N : Node_Id; Typ : Entity_Id) return Entity_Id;
   --  This routine returns the type or subtype of an array aggregate.
   --
   --    N is the array aggregate node whose type we return.
   --
   --    Typ is the context type in which N occurs.
   --
   --  This routine creates an implicit array subtype whose bounds are
   --  those defined by the aggregate. When this routine is invoked
   --  Resolve_Array_Aggregate has already processed aggregate N. Thus the
   --  Aggregate_Bounds of each sub-aggregate, is an N_Range node giving the
   --  sub-aggregate bounds. When building the aggregate itype, this function
   --  traverses the array aggregate N collecting such Aggregate_Bounds and
   --  constructs the proper array aggregate itype.
   --
   --  Note that in the case of multidimensional aggregates each inner
   --  sub-aggregate corresponding to a given array dimension, may provide a
   --  different bounds. If it is possible to determine statically that
   --  some sub-aggregates corresponding to the same index do not have the
   --  same bounds, then a warning is emitted. If such check is not possible
   --  statically (because some sub-aggregate bounds are dynamic expressions)
   --  then this job is left to the expander. In all cases the particular
   --  bounds that this function will chose for a given dimension is the first
   --  N_Range node for a sub-aggregate corresponding to that dimension.
   --
   --  Note that the Raises_Constraint_Error flag of an array aggregate
   --  whose evaluation is determined to raise CE by Resolve_Array_Aggregate,
   --  is set in Resolve_Array_Aggregate but the aggregate is not
   --  immediately replaced with a raise CE. In fact, Array_Aggr_Subtype must
   --  first construct the proper itype for the aggregate (Gigi needs
   --  this). After constructing the proper itype we will eventually replace
   --  the top-level aggregate with a raise CE (done in Resolve_Aggregate).
   --  Of course in cases such as:
   --
   --     type Arr is array (integer range <>) of Integer;
   --     A : Arr := (positive range -1 .. 2 => 0);
   --
   --  The bounds of the aggregate itype are cooked up to look reasonable
   --  (in this particular case the bounds will be 1 .. 2).

   procedure Make_String_Into_Aggregate (N : Node_Id);
   --  A string literal can appear in a context in which a one dimensional
   --  array of characters is expected. This procedure simply rewrites the
   --  string as an aggregate, prior to resolution.

   function Resolve_Null_Array_Aggregate (N : Node_Id) return Boolean;
   --  The recursive method used to construct an aggregate's bounds in
   --  Resolve_Array_Aggregate cannot work for null array aggregates. This
   --  function constructs an appropriate list of ranges and stores its first
   --  element in Aggregate_Bounds (N).

   ---------------------------------
   --  Delta aggregate processing --
   ---------------------------------

   procedure Resolve_Delta_Array_Aggregate  (N : Node_Id; Typ : Entity_Id);
   procedure Resolve_Delta_Record_Aggregate (N : Node_Id; Typ : Entity_Id);
   procedure Resolve_Deep_Delta_Assoc (N : Node_Id; Typ : Entity_Id);
   --  Resolve the names/expressions in a component association for
   --  a deep delta aggregate. Typ is the type of the enclosing object.

   ------------------------
   -- Array_Aggr_Subtype --
   ------------------------

   function Array_Aggr_Subtype
     (N   : Node_Id;
      Typ : Entity_Id) return Entity_Id
   is
      Aggr_Dimension : constant Pos := Number_Dimensions (Typ);
      --  Number of aggregate index dimensions

      Aggr_Range : array (1 .. Aggr_Dimension) of Node_Id := (others => Empty);
      --  Constrained N_Range of each index dimension in our aggregate itype

      Aggr_Low  : array (1 .. Aggr_Dimension) of Node_Id := (others => Empty);
      Aggr_High : array (1 .. Aggr_Dimension) of Node_Id := (others => Empty);
      --  Low and High bounds for each index dimension in our aggregate itype

      Is_Fully_Positional : Boolean := True;

      procedure Collect_Aggr_Bounds (N : Node_Id; Dim : Pos);
      --  N is an array (sub-)aggregate. Dim is the dimension corresponding
      --  to (sub-)aggregate N. This procedure collects and removes the side
      --  effects of the constrained N_Range nodes corresponding to each index
      --  dimension of our aggregate itype. These N_Range nodes are collected
      --  in Aggr_Range above.
      --
      --  Likewise collect in Aggr_Low & Aggr_High above the low and high
      --  bounds of each index dimension. If, when collecting, two bounds
      --  corresponding to the same dimension are static and found to differ,
      --  then emit a warning, and mark N as raising Constraint_Error.

      procedure Retrieve_Aggregate_Bounds (This_Range : Node_Id);
      --  In some cases, an appropriate list of aggregate bounds has been
      --  created during resolution. Populate Aggr_Range with that list, and
      --  remove the elements from the list so they can be added to another
      --  list later.

      -------------------------
      -- Collect_Aggr_Bounds --
      -------------------------

      procedure Collect_Aggr_Bounds (N : Node_Id; Dim : Pos) is
         This_Range : constant Node_Id := Aggregate_Bounds (N);
         --  The aggregate range node of this specific sub-aggregate

         This_Low  : constant Node_Id := Low_Bound  (This_Range);
         This_High : constant Node_Id := High_Bound (This_Range);
         --  The aggregate bounds of this specific sub-aggregate

         Assoc : Node_Id;
         Expr  : Node_Id;

      begin
         Remove_Side_Effects (This_Low,  Variable_Ref => True);
         Remove_Side_Effects (This_High, Variable_Ref => True);

         --  Collect the first N_Range for a given dimension that you find.
         --  For a given dimension they must be all equal anyway.

         if No (Aggr_Range (Dim)) then
            Aggr_Low (Dim)   := This_Low;
            Aggr_High (Dim)  := This_High;
            Aggr_Range (Dim) := This_Range;

         else
            if Compile_Time_Known_Value (This_Low) then
               if not Compile_Time_Known_Value (Aggr_Low (Dim)) then
                  Aggr_Low (Dim) := This_Low;

               elsif Expr_Value (This_Low) /= Expr_Value (Aggr_Low (Dim)) then
                  Set_Raises_Constraint_Error (N);
                  Error_Msg_Warn := SPARK_Mode /= On;
                  Error_Msg_N ("sub-aggregate low bound mismatch<<", N);
                  Error_Msg_N ("\Constraint_Error [<<", N);
               end if;
            end if;

            if Compile_Time_Known_Value (This_High) then
               if not Compile_Time_Known_Value (Aggr_High (Dim)) then
                  Aggr_High (Dim) := This_High;

               elsif
                 Expr_Value (This_High) /= Expr_Value (Aggr_High (Dim))
               then
                  Set_Raises_Constraint_Error (N);
                  Error_Msg_Warn := SPARK_Mode /= On;
                  Error_Msg_N ("sub-aggregate high bound mismatch<<", N);
                  Error_Msg_N ("\Constraint_Error [<<", N);
               end if;
            end if;
         end if;

         if Dim < Aggr_Dimension then

            if not Is_Null_Aggregate (N) then

               --  Process positional components

               if Present (Expressions (N)) then
                  Expr := First (Expressions (N));
                  while Present (Expr) loop
                     Collect_Aggr_Bounds (Expr, Dim + 1);
                     Next (Expr);
                  end loop;
               end if;

               --  Process component associations

               if Present (Component_Associations (N)) then
                  Is_Fully_Positional := False;

                  Assoc := First (Component_Associations (N));
                  while Present (Assoc) loop
                     Expr := Expression (Assoc);
                     Collect_Aggr_Bounds (Expr, Dim + 1);

                     --  Propagate the error; it is not done in other cases to
                     --  avoid replacing this aggregate by a CE node (required
                     --  to report complementary warnings when the expression
                     --  is resolved).

                     if Is_Null_Aggregate (Expr)
                       and then Raises_Constraint_Error (Expr)
                     then
                        Set_Raises_Constraint_Error (N);
                     end if;

                     Next (Assoc);
                  end loop;
               end if;

            --  For null aggregates, build the bounds of their inner dimensions
            --  since they are required for building the aggregate itype.

            else
               declare
                  Loc        : constant Source_Ptr := Sloc (N);
                  Typ        : constant Entity_Id := Etype (N);
                  Index      : Node_Id;
                  Index_Typ  : Entity_Id;
                  Lo, Hi     : Node_Id;
                  Null_Range : Node_Id;
                  Num_Dim    : Pos := 1;

               begin
                  --  Move the index to the first dimension implicitly included
                  --  in this null aggregate.

                  Index := First_Index (Typ);
                  while Num_Dim <= Dim loop
                     Next_Index (Index);
                     Num_Dim := Num_Dim + 1;
                  end loop;

                  while Present (Index) loop
                     Get_Index_Bounds (Index, L => Lo, H => Hi);
                     Index_Typ := Etype (Index);

                     if Cannot_Compute_High_Bound (Index) then
                        --  To avoid reporting spurious errors we use the upper
                        --  bound as the higger bound of this index; this value
                        --  will not be used to generate code because this
                        --  aggregate will be replaced by a raise CE node.

                        Hi := New_Copy_Tree (Lo);

                        if not Raises_Constraint_Error (N) then
                           Report_Null_Array_Constraint_Error (N, Index_Typ);
                           Set_Raises_Constraint_Error (N);
                        end if;

                     else
                        --  The upper bound is the predecessor of the lower
                        --  bound.

                        Hi := Make_Attribute_Reference (Loc,
                                Prefix => New_Occurrence_Of (Index_Typ, Loc),
                                Attribute_Name => Name_Pred,
                                Expressions => New_List (New_Copy_Tree (Lo)));
                     end if;

                     Null_Range := Make_Range (Loc, New_Copy_Tree (Lo), Hi);
                     Analyze_And_Resolve (Null_Range, Index_Typ);

                     Aggr_Low (Num_Dim)   := Low_Bound (Null_Range);
                     Aggr_High (Num_Dim)  := High_Bound (Null_Range);
                     Aggr_Range (Num_Dim) := Null_Range;

                     Num_Dim := Num_Dim + 1;
                     Next_Index (Index);
                  end loop;

                  pragma Assert (Num_Dim = Aggr_Dimension + 1);
               end;
            end if;
         end if;
      end Collect_Aggr_Bounds;

      -------------------------------
      -- Retrieve_Aggregate_Bounds --
      -------------------------------

      procedure Retrieve_Aggregate_Bounds (This_Range : Node_Id) is
         R : Node_Id := This_Range;
      begin
         for J in 1 .. Aggr_Dimension loop
            Aggr_Range (J) := R;
            Next_Index (R);

            --  Remove bounds from the list, so they can be reattached as
            --  the First_Index/Next_Index again.

            Remove (Aggr_Range (J));
         end loop;
      end Retrieve_Aggregate_Bounds;

      --  Array_Aggr_Subtype variables

      Itype : Entity_Id;
      --  The final itype of the overall aggregate

      Index_Constraints : constant List_Id := New_List;
      --  The list of index constraints of the aggregate itype

   --  Start of processing for Array_Aggr_Subtype

   begin
      --  Make sure that the list of index constraints is properly attached to
      --  the tree, and then collect the aggregate bounds.

      --  If no aggregate bounds have been set, this is an aggregate with
      --  iterator specifications and a dynamic size to be determined by
      --  first pass of expanded code.

      if No (Aggregate_Bounds (N)) then
         return Typ;
      end if;

      Set_Parent (Index_Constraints, N);

      if Is_Rewrite_Substitution (N)
        and then Present (Component_Associations (Original_Node (N)))
      then
         Retrieve_Aggregate_Bounds (First_Index (Etype (Original_Node (N))));

      --  When resolving a null aggregate we created a list of aggregate bounds
      --  for the consecutive dimensions. The bounds for the first dimension
      --  are attached as the Aggregate_Bounds of the aggregate node.

      elsif Is_Null_Aggregate (N) then
         Retrieve_Aggregate_Bounds (Aggregate_Bounds (N));
      else
         Collect_Aggr_Bounds (N, 1);
      end if;

      --  Build the list of constrained indexes of our aggregate itype

      for J in 1 .. Aggr_Dimension loop
         Create_Index : declare
            Index_Base : constant Entity_Id :=
                           Base_Type (Etype (Aggr_Range (J)));
            Index_Typ  : Entity_Id;

         begin
            --  Construct the Index subtype, and associate it with the range
            --  construct that generates it.

            Index_Typ :=
              Create_Itype (Subtype_Kind (Ekind (Index_Base)), Aggr_Range (J));

            Set_Etype (Index_Typ, Index_Base);

            if Is_Character_Type (Index_Base) then
               Set_Is_Character_Type (Index_Typ);
            end if;

            Set_Size_Info      (Index_Typ,                (Index_Base));
            Set_RM_Size        (Index_Typ, RM_Size        (Index_Base));
            Set_First_Rep_Item (Index_Typ, First_Rep_Item (Index_Base));
            Set_Scalar_Range   (Index_Typ, Aggr_Range (J));

            if Is_Discrete_Or_Fixed_Point_Type (Index_Typ) then
               Set_RM_Size (Index_Typ, UI_From_Int (Minimum_Size (Index_Typ)));
            end if;

            Set_Etype (Aggr_Range (J), Index_Typ);

            Append (Aggr_Range (J), To => Index_Constraints);
         end Create_Index;
      end loop;

      --  Now build the Itype

      Itype := Create_Itype (E_Array_Subtype, N);

      Set_First_Rep_Item         (Itype, First_Rep_Item        (Typ));
      Set_Convention             (Itype, Convention            (Typ));
      Set_Depends_On_Private     (Itype, Has_Private_Component (Typ));
      Set_Etype                  (Itype, Base_Type             (Typ));
      Set_Has_Alignment_Clause   (Itype, Has_Alignment_Clause  (Typ));
      Set_Is_Aliased             (Itype, Is_Aliased            (Typ));
      Set_Is_Independent         (Itype, Is_Independent        (Typ));
      Set_Depends_On_Private     (Itype, Depends_On_Private    (Typ));

      Copy_Suppress_Status (Index_Check,  Typ, Itype);
      Copy_Suppress_Status (Length_Check, Typ, Itype);

      Set_First_Index    (Itype, First (Index_Constraints));
      Set_Is_Constrained (Itype, True);
      Set_Is_Internal    (Itype, True);

      if Has_Predicates (Typ) then
         Set_Has_Predicates (Itype);

         --  If the base type has a predicate, capture the predicated parent
         --  or the existing predicate function for SPARK use.

         if Present (Predicate_Function (Typ)) then
            Set_Predicate_Function (Itype, Predicate_Function (Typ));

         elsif Is_Itype (Typ) then
            Set_Predicated_Parent (Itype, Predicated_Parent (Typ));

         else
            Set_Predicated_Parent (Itype, Typ);
         end if;
      end if;

      --  A simple optimization: purely positional aggregates of static
      --  components should be passed to gigi unexpanded whenever possible, and
      --  regardless of the staticness of the bounds themselves. Subsequent
      --  checks in exp_aggr verify that type is not packed, etc.

      Set_Size_Known_At_Compile_Time
        (Itype,
         Is_Fully_Positional
           and then Comes_From_Source (N)
           and then Size_Known_At_Compile_Time (Component_Type (Typ)));

      --  We always need a freeze node for a packed array subtype, so that we
      --  can build the Packed_Array_Impl_Type corresponding to the subtype. If
      --  expansion is disabled, the packed array subtype is not built, and we
      --  must not generate a freeze node for the type, or else it will appear
      --  incomplete to gigi.

      if Is_Packed (Itype)
        and then not In_Spec_Expression
        and then Expander_Active
      then
         Freeze_Itype (Itype, N);
      end if;

      return Itype;
   end Array_Aggr_Subtype;

   -------------------------------
   -- Cannot_Compute_High_Bound --
   -------------------------------

   function Cannot_Compute_High_Bound (Index : Entity_Id) return Boolean is
      Index_Type : constant Entity_Id := Etype (Index);
      Lo, Hi     : Node_Id;

   begin
      if not Is_Modular_Integer_Type (Index_Type)
        and then not Is_Enumeration_Type (Index_Type)
      then
         return False;

      elsif Index_Type = Base_Type (Index_Type) then
         return True;

      else
         Get_Index_Bounds (Index, L => Lo, H => Hi);

         if Compile_Time_Known_Value (Lo) then
            if Is_Enumeration_Type (Index_Type)
              and then not Is_Character_Type (Index_Type)
            then
               return Enumeration_Pos (Entity (Lo))
                 = Enumeration_Pos (First_Literal (Base_Type (Index_Type)));
            else
               return Expr_Value (Lo) = Uint_0;
            end if;
         end if;
      end if;

      return False;
   end Cannot_Compute_High_Bound;

   --------------------------------
   -- Check_Misspelled_Component --
   --------------------------------

   procedure Check_Misspelled_Component
     (Elements  : Elist_Id;
      Component : Node_Id)
   is
      Max_Suggestions   : constant := 2;

      Nr_Of_Suggestions : Natural := 0;
      Suggestion_1      : Entity_Id := Empty;
      Suggestion_2      : Entity_Id := Empty;
      Component_Elmt    : Elmt_Id;

   begin
      --  All the components of List are matched against Component and a count
      --  is maintained of possible misspellings. When at the end of the
      --  analysis there are one or two (not more) possible misspellings,
      --  these misspellings will be suggested as possible corrections.

      Component_Elmt := First_Elmt (Elements);
      while Nr_Of_Suggestions <= Max_Suggestions
        and then Present (Component_Elmt)
      loop
         if Is_Bad_Spelling_Of
              (Chars (Node (Component_Elmt)),
               Chars (Component))
         then
            Nr_Of_Suggestions := Nr_Of_Suggestions + 1;

            case Nr_Of_Suggestions is
               when 1      => Suggestion_1 := Node (Component_Elmt);
               when 2      => Suggestion_2 := Node (Component_Elmt);
               when others => null;
            end case;
         end if;

         Next_Elmt (Component_Elmt);
      end loop;

      --  Report at most two suggestions

      if Nr_Of_Suggestions = 1 then
         Error_Msg_NE -- CODEFIX
           ("\possible misspelling of&", Component, Suggestion_1);

      elsif Nr_Of_Suggestions = 2 then
         Error_Msg_Node_2 := Suggestion_2;
         Error_Msg_NE -- CODEFIX
           ("\possible misspelling of& or&", Component, Suggestion_1);
      end if;
   end Check_Misspelled_Component;

   ----------------------------------------
   -- Check_Expr_OK_In_Limited_Aggregate --
   ----------------------------------------

   procedure Check_Expr_OK_In_Limited_Aggregate (Expr : Node_Id) is
   begin
      if Is_Limited_Type (Etype (Expr))
         and then Comes_From_Source (Expr)
      then
         if In_Instance_Body or else In_Inlined_Body then
            null;

         elsif not OK_For_Limited_Init (Etype (Expr), Expr) then
            Error_Msg_N
              ("initialization not allowed for limited types", Expr);
            Explain_Limited_Type (Etype (Expr), Expr);
         end if;
      end if;
   end Check_Expr_OK_In_Limited_Aggregate;

   --------------------
   -- Is_Deep_Choice --
   --------------------

   function Is_Deep_Choice
     (Choice    : Node_Id;
      Aggr_Type : Type_Kind_Id) return Boolean
   is
      Pref : Node_Id := Choice;
   begin
      while not Is_Root_Prefix_Of_Deep_Choice (Pref) loop
         Pref := Prefix (Pref);
      end loop;

      if Is_Array_Type (Aggr_Type) then
         return Paren_Count (Pref) > 0
           and then Pref /= Choice;
      else
         return Pref /= Choice;
      end if;
   end Is_Deep_Choice;

   --------------------------
   -- Is_Indexed_Aggregate --
   --------------------------

   function Is_Indexed_Aggregate
     (N           : N_Aggregate_Id;
      Add_Unnamed : Node_Id;
      New_Indexed : Node_Id) return Boolean
   is
   begin
      if Present (New_Indexed)
        and then not Is_Null_Aggregate (N)
      then
         if No (Add_Unnamed) then
            return True;

         else
            declare
               Comp_Assns : constant List_Id := Component_Associations (N);
               Comp_Assn  : Node_Id;

            begin
               if not Is_Empty_List (Comp_Assns) then

                  --  It suffices to look at the first association to determine
                  --  whether the aggregate is an indexed aggregate.

                  Comp_Assn := First (Comp_Assns);

                  --  Test for the component association being either:
                  --
                  --    1) an N_Component_Association node, in which case there
                  --       is a list of choices (the "key choices");
                  --
                  --  or else:
                  --
                  --    2) an N_Iterated_Component_Association node that has
                  --       a Defining_Identifier, in which case it has
                  --       Discrete_Choices that effectively make it
                  --       equivalent to a Loop_Parameter_Specification;
                  --
                  --  or else:
                  --
                  --    3) an N_Iterated_Element_Association node with
                  --       a Loop_Parameter_Specification with a discrete
                  --       subtype or range.
                  --
                  --  This basically corresponds to the definition of indexed
                  --  aggregates (in RM22 4.3.5(25/5)), but the GNAT tree
                  --  representation doesn't always directly match the RM
                  --  syntax for various reasons.

                  if Nkind (Comp_Assn) = N_Component_Association
                    or else
                      (Nkind (Comp_Assn) = N_Iterated_Component_Association
                        and then Present (Defining_Identifier (Comp_Assn)))
                  then
                     return True;

                  --  In the case of an iterated_element_association with a
                  --  loop_parameter_specification, we have to look deeper to
                  --  confirm that it is not actually an iterator_specification
                  --  masquerading as a loop_parameter_specification. Those can
                  --  share syntax (for example, having the iterator of form
                  --  "for C in <function-call>") and a rewrite into an
                  --  iterator_specification can happen later.

                  elsif Nkind (Comp_Assn) = N_Iterated_Element_Association
                    and then Present (Loop_Parameter_Specification (Comp_Assn))
                  then
                     declare
                        Loop_Parm_Spec  : constant Node_Id :=
                          Loop_Parameter_Specification (Comp_Assn);
                        Discr_Subt_Defn : constant Node_Id :=
                          Discrete_Subtype_Definition (Loop_Parm_Spec);
                     begin
                        if Nkind (Discr_Subt_Defn) = N_Range
                          or else
                            Nkind (Discr_Subt_Defn) = N_Subtype_Indication
                          or else
                            (Is_Entity_Name (Discr_Subt_Defn)
                              and then
                             Is_Type (Entity (Discr_Subt_Defn)))
                        then
                           return True;
                        end if;
                     end;
                  end if;
               end if;
            end;
         end if;
      end if;

      return False;
   end Is_Indexed_Aggregate;

   -------------------------
   -- Is_Others_Aggregate --
   -------------------------

   function Is_Others_Aggregate (Aggr : Node_Id) return Boolean is
      Assoc : constant List_Id := Component_Associations (Aggr);

   begin
      return No (Expressions (Aggr))
        and then Nkind (First (Choice_List (First (Assoc)))) = N_Others_Choice;
   end Is_Others_Aggregate;

   -----------------------------------
   -- Is_Root_Prefix_Of_Deep_Choice --
   -----------------------------------

   function Is_Root_Prefix_Of_Deep_Choice (Pref : Node_Id) return Boolean is
   begin
      return Paren_Count (Pref) > 0
        or else Nkind (Pref) not in N_Indexed_Component
                                  | N_Selected_Component;
   end Is_Root_Prefix_Of_Deep_Choice;

   -------------------------
   -- Is_Single_Aggregate --
   -------------------------

   function Is_Single_Aggregate (Aggr : Node_Id) return Boolean is
      Assoc : constant List_Id := Component_Associations (Aggr);

   begin
      return No (Expressions (Aggr))
        and then No (Next (First (Assoc)))
        and then No (Next (First (Choice_List (First (Assoc)))));
   end Is_Single_Aggregate;

   -----------------------
   -- Is_Null_Aggregate --
   -----------------------

   function Is_Null_Aggregate (N : Node_Id) return Boolean is
   begin
      return Nkind (N) = N_Aggregate
        and then Is_Homogeneous_Aggregate (N)
        and then Is_Empty_List (Expressions (N))
        and then Is_Empty_List (Component_Associations (N));
   end Is_Null_Aggregate;

   ----------------------------------------
   -- Is_Null_Array_Aggregate_High_Bound --
   ----------------------------------------

   function Is_Null_Array_Aggregate_High_Bound (N : Node_Id) return Boolean is
      Original_N : constant Node_Id := Original_Node (N);
   begin
      return Ada_Version >= Ada_2022
        and then not Comes_From_Source (Original_N)
        and then Nkind (Original_N) = N_Attribute_Reference
        and then
          Get_Attribute_Id (Attribute_Name (Original_N)) = Attribute_Pred
        and then Nkind (Parent (N)) in N_Range | N_Op_Le
        and then not Comes_From_Source (Parent (N));
   end Is_Null_Array_Aggregate_High_Bound;

   --------------------------------
   -- Make_String_Into_Aggregate --
   --------------------------------

   procedure Make_String_Into_Aggregate (N : Node_Id) is
      Exprs  : constant List_Id    := New_List;
      Loc    : constant Source_Ptr := Sloc (N);
      Str    : constant String_Id  := Strval (N);
      Strlen : constant Nat        := String_Length (Str);
      C      : Char_Code;
      C_Node : Node_Id;
      New_N  : Node_Id;
      P      : Source_Ptr;

   begin
      P := Loc + 1;
      for J in 1 .. Strlen loop
         C := Get_String_Char (Str, J);
         Set_Character_Literal_Name (C);

         C_Node :=
           Make_Character_Literal (P,
             Chars              => Name_Find,
             Char_Literal_Value => UI_From_CC (C));
         Set_Etype (C_Node, Any_Character);
         Append_To (Exprs, C_Node);

         P := P + 1;
         --  Something special for wide strings???
      end loop;

      New_N := Make_Aggregate (Loc, Expressions => Exprs);
      Set_Analyzed (New_N);
      Set_Etype (New_N, Any_Composite);

      Rewrite (N, New_N);
   end Make_String_Into_Aggregate;

   ----------------------------------------
   -- Report_Null_Array_Constraint_Error --
   ----------------------------------------

   procedure Report_Null_Array_Constraint_Error
     (N         : Node_Id;
      Index_Typ : Entity_Id) is
   begin
      Error_Msg_Warn := SPARK_Mode /= On;

      if Is_Modular_Integer_Type (Index_Typ) then
         Error_Msg_N
           ("null array aggregate indexed by a modular type<<", N);
      else
         Error_Msg_N
           ("null array aggregate indexed by an enumeration type<<", N);
      end if;

      Error_Msg_N ("\Constraint_Error [<<", N);
   end Report_Null_Array_Constraint_Error;

   -----------------------
   -- Resolve_Aggregate --
   -----------------------

   procedure Resolve_Aggregate (N : Node_Id; Typ : Entity_Id) is
      Loc : constant Source_Ptr := Sloc (N);

      Aggr_Subtyp : Entity_Id;
      --  The actual aggregate subtype. This is not necessarily the same as Typ
      --  which is the subtype of the context in which the aggregate was found.

      Others_Box : Boolean := False;
      --  Set to True if N represents a simple aggregate with only
      --  (others => <>), not nested as part of another aggregate.

      function Is_Full_Access_Aggregate (N : Node_Id) return Boolean;
      --  If a full access object is initialized with an aggregate or is
      --  assigned an aggregate, we have to prevent a piecemeal access or
      --  assignment to the object, even if the aggregate is to be expanded.
      --  We create a temporary for the aggregate, and assign the temporary
      --  instead, so that the back end can generate an atomic move for it.
      --  This is only done in the context of an object declaration or an
      --  assignment. Function is a noop and returns false in other contexts.

      function Within_Aggregate (N : Node_Id) return Boolean;
      --  Return True if N is part of an N_Aggregate

      ------------------------------
      -- Is_Full_Access_Aggregate --
      ------------------------------

      function Is_Full_Access_Aggregate (N : Node_Id) return Boolean is
         Loc : constant Source_Ptr := Sloc (N);

         New_N : Node_Id;
         Par   : Node_Id;
         Temp  : Entity_Id;
         Typ   : Entity_Id;

      begin
         Par := Parent (N);

         --  Aggregate may be qualified, so find outer context

         if Nkind (Par) = N_Qualified_Expression then
            Par := Parent (Par);
         end if;

         if not Comes_From_Source (Par) then
            return False;
         end if;

         case Nkind (Par) is
            when N_Assignment_Statement =>
               Typ := Etype (Name (Par));

               if not Is_Full_Access (Typ)
                 and then not Is_Full_Access_Object (Name (Par))
               then
                  return False;
               end if;

            when N_Object_Declaration =>
               Typ := Etype (Defining_Identifier (Par));

               if not Is_Full_Access (Typ)
                 and then not Is_Full_Access (Defining_Identifier (Par))
               then
                  return False;
               end if;

            when others =>
               return False;
         end case;

         Temp := Make_Temporary (Loc, 'T', N);
         New_N :=
           Make_Object_Declaration (Loc,
             Defining_Identifier => Temp,
             Constant_Present    => True,
             Object_Definition   => New_Occurrence_Of (Typ, Loc),
             Expression          => Relocate_Node (N));
         Insert_Action (Par, New_N);

         Rewrite (N, New_Occurrence_Of (Temp, Loc));
         Analyze_And_Resolve (N, Typ);

         return True;
      end Is_Full_Access_Aggregate;

      ----------------------
      -- Within_Aggregate --
      ----------------------

      function Within_Aggregate (N : Node_Id) return Boolean is
         P : Node_Id := Parent (N);
      begin
         while Present (P) loop
            if Nkind (P) = N_Aggregate then
               return True;
            end if;

            P := Parent (P);
         end loop;

         return False;
      end Within_Aggregate;

   --  Start of processing for Resolve_Aggregate

   begin
      --  Ignore junk empty aggregate resulting from parser error

      if No (Expressions (N))
        and then No (Component_Associations (N))
        and then not Null_Record_Present (N)
      then
         return;

      --  If the aggregate is assigned to a full access variable, we have
      --  to prevent a piecemeal assignment even if the aggregate is to be
      --  expanded. We create a temporary for the aggregate, and assign the
      --  temporary instead, so that the back end can generate an atomic move
      --  for it. This is properly an expansion activity but it must be done
      --  before resolution because aggregate resolution cannot be done twice.

      elsif Expander_Active and then Is_Full_Access_Aggregate (N) then
         return;
      end if;

      --  If the aggregate has box-initialized components, its type must be
      --  frozen so that initialization procedures can properly be called
      --  in the resolution that follows. The replacement of boxes with
      --  initialization calls is properly an expansion activity but it must
      --  be done during resolution.

      if Expander_Active
        and then Present (Component_Associations (N))
      then
         declare
            Comp       : Node_Id;
            First_Comp : Boolean := True;

         begin
            Comp := First (Component_Associations (N));
            while Present (Comp) loop
               if Box_Present (Comp) then
                  if First_Comp
                    and then No (Expressions (N))
                    and then Nkind (First (Choices (Comp))) = N_Others_Choice
                    and then not Within_Aggregate (N)
                  then
                     Others_Box := True;
                  end if;

                  Insert_Actions (N, Freeze_Entity (Typ, N));
                  exit;
               end if;

               First_Comp := False;
               Next (Comp);
            end loop;
         end;
      end if;

      --  Check for aggregates not allowed in configurable run-time mode.
      --  We allow all cases of aggregates that do not come from source, since
      --  these are all assumed to be small (e.g. bounds of a string literal).
      --  We also allow aggregates of types we know to be small.

      if not Support_Aggregates_On_Target
        and then Comes_From_Source (N)
        and then (not Known_Static_Esize (Typ)
                   or else Esize (Typ) > System_Max_Integer_Size)
      then
         Error_Msg_CRT ("aggregate", N);
      end if;

      --  Ada 2005 (AI-287): Limited aggregates allowed

      --  In an instance, ignore aggregate subcomponents that may be limited,
      --  because they originate in view conflicts. If the original aggregate
      --  is legal and the actuals are legal, the aggregate itself is legal.

      if Is_Limited_Type (Typ)
        and then Ada_Version < Ada_2005
        and then not In_Instance
      then
         Error_Msg_N ("aggregate type cannot be limited", N);
         Explain_Limited_Type (Typ, N);

      elsif Is_Class_Wide_Type (Typ) then
         Error_Msg_N ("type of aggregate cannot be class-wide", N);

      elsif Typ = Any_String
        or else Typ = Any_Composite
      then
         Error_Msg_N ("no unique type for aggregate", N);
         Set_Etype (N, Any_Composite);

      elsif Is_Array_Type (Typ) and then Null_Record_Present (N) then
         Error_Msg_N ("null record forbidden in array aggregate", N);

      elsif Is_Record_Type (Typ)
        and then not Is_Homogeneous_Aggregate (N)
      then
         Resolve_Record_Aggregate (N, Typ);

      elsif Has_Aspect (Typ, Aspect_Aggregate)
        and then Ada_Version >= Ada_2022
      then
         --  Check for Ada 2022 and () aggregate.

         if not Is_Homogeneous_Aggregate (N) then
            Error_Msg_N ("container aggregate must use '['], not ()", N);
         end if;

         Resolve_Container_Aggregate (N, Typ);

      --  Check for an attempt to use "[]" for an aggregate of a record type
      --  after handling the case where the type has an Aggregate aspect,
      --  because the aspect can be specified for record types, but if it
      --  wasn't specified, then this is an error.

      elsif Is_Record_Type (Typ) and then Is_Homogeneous_Aggregate (N) then
         Error_Msg_N ("record aggregate must use (), not '[']", N);

      elsif Is_Array_Type (Typ) then

         --  First a special test, for the case of a positional aggregate of
         --  characters which can be replaced by a string literal.

         --  Do not perform this transformation if this was a string literal
         --  to start with, whose components needed constraint checks, or if
         --  the component type is nonstatic or has predicates, because it will
         --  require those checks and be transformed back into an aggregate.
         --  If the index type is not Integer, then the aggregate may represent
         --  a user-defined string type but the context might need the original
         --  type, so we do not perform the transformation at this point.

         if Number_Dimensions (Typ) = 1
           and then Is_Standard_Character_Type (Component_Type (Typ))
           and then No (Component_Associations (N))
           and then not Is_Limited_Composite (Typ)
           and then not Is_Private_Composite (Typ)
           and then not Is_Bit_Packed_Array (Typ)
           and then Nkind (Original_Node (Parent (N))) /= N_String_Literal
           and then Is_OK_Static_Subtype (Component_Type (Typ))
           and then not Has_Predicates (Component_Type (Typ))
           and then Base_Type (Etype (First_Index (Typ))) =
                      Base_Type (Standard_Integer)
           and then not Has_Static_Empty_Array_Bounds (Typ)
         then
            declare
               Expr : Node_Id;

            begin
               Expr := First (Expressions (N));
               while Present (Expr) loop
                  exit when Nkind (Expr) /= N_Character_Literal;
                  Next (Expr);
               end loop;

               if No (Expr) then
                  Start_String;

                  Expr := First (Expressions (N));
                  while Present (Expr) loop
                     Store_String_Char (UI_To_CC (Char_Literal_Value (Expr)));
                     Next (Expr);
                  end loop;

                  Rewrite (N, Make_String_Literal (Loc, End_String));

                  Analyze_And_Resolve (N, Typ);
                  return;
               end if;
            end;
         end if;

         --  Here if we have a real aggregate to deal with

         Array_Aggregate : declare
            Aggr_Resolved : Boolean;
            Aggr_Typ : constant Entity_Id := Etype (Typ);
            --  This is the unconstrained array type, which is the type against
            --  which the aggregate is to be resolved. Typ itself is the array
            --  type of the context which may not be the same subtype as the
            --  subtype for the final aggregate.

            Is_Null_Aggr : constant Boolean := Is_Null_Aggregate (N);

         begin
            --  In the following we determine whether an OTHERS choice is
            --  allowed inside the array aggregate. The test checks the context
            --  in which the array aggregate occurs. If the context does not
            --  permit it, or the aggregate type is unconstrained, an OTHERS
            --  choice is not allowed (except that it is always allowed on the
            --  right-hand side of an assignment statement; in this case the
            --  constrainedness of the type doesn't matter, because an array
            --  object is always constrained).

            --  If expansion is disabled (generic context, or semantics-only
            --  mode) actual subtypes cannot be constructed, and the type of an
            --  object may be its unconstrained nominal type. However, if the
            --  context is an assignment statement, OTHERS is allowed, because
            --  the target of the assignment will have a constrained subtype
            --  when fully compiled. Ditto if the context is an initialization
            --  procedure where a component may have a predicate function that
            --  carries the base type.

            --  Note that there is no node for Explicit_Actual_Parameter.
            --  To test for this context we therefore have to test for node
            --  N_Parameter_Association which itself appears only if there is a
            --  formal parameter. Consequently we also need to test for
            --  N_Procedure_Call_Statement or N_Function_Call.

            --  The context may be an N_Reference node, created by expansion.
            --  Legality of the others clause was established in the source,
            --  so the context is legal.

            Set_Etype (N, Aggr_Typ);  --  May be overridden later on

            if Is_Null_Aggr then
               Set_Etype (N, Typ);
               Aggr_Resolved := Resolve_Null_Array_Aggregate (N);

            elsif Nkind (Parent (N)) = N_Assignment_Statement
              or else Inside_Init_Proc
              or else (Is_Constrained (Typ)
                        and then Nkind (Parent (N)) in
                                   N_Parameter_Association
                                 | N_Function_Call
                                 | N_Procedure_Call_Statement
                                 | N_Generic_Association
                                 | N_Formal_Object_Declaration
                                 | N_Simple_Return_Statement
                                 | N_Object_Declaration
                                 | N_Component_Declaration
                                 | N_Parameter_Specification
                                 | N_Qualified_Expression
                                 | N_Unchecked_Type_Conversion
                                 | N_Reference
                                 | N_Aggregate
                                 | N_Extension_Aggregate
                                 | N_Component_Association
                                 | N_Case_Expression_Alternative
                                 | N_If_Expression
                                 | N_Expression_With_Actions)
            then
               Aggr_Resolved :=
                 Resolve_Array_Aggregate
                   (N,
                    Index          => First_Index (Aggr_Typ),
                    Index_Constr   => First_Index (Typ),
                    Component_Typ  => Component_Type (Typ),
                    Iterated       => False,
                    Others_Allowed => True);
            else
               Aggr_Resolved :=
                 Resolve_Array_Aggregate
                   (N,
                    Index          => First_Index (Aggr_Typ),
                    Index_Constr   => First_Index (Aggr_Typ),
                    Component_Typ  => Component_Type (Typ),
                    Iterated       => False,
                    Others_Allowed => False);
            end if;

            if not Aggr_Resolved then

               --  A parenthesized expression may have been intended as an
               --  aggregate, leading to a type error when analyzing the
               --  component. This can also happen for a nested component
               --  (see Analyze_Aggr_Expr).

               if Paren_Count (N) > 0 then
                  Error_Msg_N
                    ("positional aggregate cannot have one component", N);
               end if;

               Aggr_Subtyp := Any_Composite;

            else
               Aggr_Subtyp := Array_Aggr_Subtype (N, Typ);
            end if;

            Set_Etype (N, Aggr_Subtyp);
         end Array_Aggregate;

      elsif Is_Private_Type (Typ)
        and then Present (Full_View (Typ))
        and then (In_Inlined_Body or In_Instance_Body)
        and then Is_Composite_Type (Full_View (Typ))
      then
         Resolve (N, Full_View (Typ));

      else
         Error_Msg_N ("illegal context for aggregate", N);
      end if;

      --  If we can determine statically that the evaluation of the aggregate
      --  raises Constraint_Error, then replace the aggregate with an
      --  N_Raise_Constraint_Error node, but set the Etype to the right
      --  aggregate subtype. Gigi needs this.

      if Raises_Constraint_Error (N) then
         Aggr_Subtyp := Etype (N);
         Rewrite (N,
           Make_Raise_Constraint_Error (Loc, Reason => CE_Range_Check_Failed));
         Set_Raises_Constraint_Error (N);
         Set_Etype (N, Aggr_Subtyp);
         Set_Analyzed (N);
      end if;

      if Warn_On_No_Value_Assigned
        and then Others_Box
        and then not Is_Fully_Initialized_Type (Etype (N))
      then
         Error_Msg_N ("?v?aggregate not fully initialized", N);
      end if;

      Check_Function_Writable_Actuals (N);
   end Resolve_Aggregate;

   -----------------------------
   -- Resolve_Array_Aggregate --
   -----------------------------

   function Resolve_Array_Aggregate
     (N              : Node_Id;
      Index          : Node_Id;
      Index_Constr   : Node_Id;
      Component_Typ  : Entity_Id;
      Iterated       : Boolean;
      Others_Allowed : Boolean) return Boolean
   is
      Loc : constant Source_Ptr := Sloc (N);

      Failure : constant Boolean := False;
      Success : constant Boolean := True;

      Ctyp : constant Entity_Id :=
        Get_Corresponding_Mutably_Tagged_Type_If_Present (Component_Typ);

      Index_Typ      : constant Entity_Id := Etype (Index);
      Index_Typ_Low  : constant Node_Id   := Type_Low_Bound  (Index_Typ);
      Index_Typ_High : constant Node_Id   := Type_High_Bound (Index_Typ);
      --  The type of the index corresponding to the array sub-aggregate along
      --  with its low and upper bounds.

      Index_Base      : constant Entity_Id := Base_Type (Index_Typ);
      Index_Base_Low  : constant Node_Id   := Type_Low_Bound (Index_Base);
      Index_Base_High : constant Node_Id   := Type_High_Bound (Index_Base);
      --  Ditto for the base type

      Others_N : Node_Id := Empty;

      Nb_Choices : Nat := 0;
      --  Contains the overall number of named choices in this sub-aggregate

      Saved_SED  : constant Nat := Serious_Errors_Detected;

      function Add (Val : Uint; To : Node_Id) return Node_Id;
      --  Creates a new expression node where Val is added to expression To.
      --  Tries to constant fold whenever possible. To must be an already
      --  analyzed expression.

      procedure Check_Bound (BH : Node_Id; AH : in out Node_Id);
      --  Checks that AH (the upper bound of an array aggregate) is less than
      --  or equal to BH (the upper bound of the index base type). If the check
      --  fails, a warning is emitted, the Raises_Constraint_Error flag of N is
      --  set, and AH is replaced with a duplicate of BH.

      procedure Check_Bounds (L, H : Node_Id; AL, AH : Node_Id);
      --  Checks that range AL .. AH is compatible with range L .. H. Emits a
      --  warning if not and sets the Raises_Constraint_Error flag in N.

      procedure Check_Length (L, H : Node_Id; Len : Uint);
      --  Checks that range L .. H contains at least Len elements. Emits a
      --  warning if not and sets the Raises_Constraint_Error flag in N.

      function Dynamic_Or_Null_Range (L, H : Node_Id) return Boolean;
      --  Returns True if range L .. H is dynamic or null

      procedure Get (Value : out Uint; From : Node_Id; OK : out Boolean);
      --  Given expression node From, this routine sets OK to False if it
      --  cannot statically evaluate From. Otherwise it stores this static
      --  value into Value.

      function Has_Null_Aggregate_Raising_Constraint_Error
        (Expr : Node_Id) return Boolean;
      --  Determines if the given expression has some null aggregate that will
      --  cause raising CE at runtime.

      function Resolve_Aggr_Expr
        (Expr          : Node_Id;
         Iterated_Elmt : Boolean := False;
         Single_Elmt   : Boolean := True) return Boolean;
      --  Resolves aggregate expression Expr. Returns False if resolution
      --  fails. If Single_Elmt is set to False, the expression Expr may be
      --  used to initialize several array aggregate elements (this can happen
      --  for discrete choices such as "L .. H => Expr" or the OTHERS choice).
      --  In this event we do not resolve Expr unless expansion is disabled.
      --  To know why, see the DELAYED COMPONENT RESOLUTION note above.

      function Resolve_Iterated_Component_Association
        (N         : Node_Id;
         Index_Typ : Entity_Id) return Boolean;
      --  For AI12-061: resolves iterated component association N of Index_Typ.
      --  Returns False if resolution fails.

      function Subtract (Val : Uint; To : Node_Id) return Node_Id;
      --  Creates a new expression node where Val is subtracted to expression
      --  To. Tries to constant fold whenever possible. To must be an already
      --  analyzed expression.

      procedure Warn_On_Null_Component_Association (Expr : Node_Id);
      --  Expr is either a conditional expression or a case expression of an
      --  iterated component association initializing the aggregate N with
      --  components that can never be null. Report warning on associations
      --  that may initialize some component with a null value.

      ---------
      -- Add --
      ---------

      function Add (Val : Uint; To : Node_Id) return Node_Id is
         Expr_Pos : Node_Id;
         Expr     : Node_Id;
         To_Pos   : Node_Id;

      begin
         if Raises_Constraint_Error (To) then
            return To;
         end if;

         --  First test if we can do constant folding

         if Compile_Time_Known_Value (To)
           or else Nkind (To) = N_Integer_Literal
         then
            Expr_Pos := Make_Integer_Literal (Loc, Expr_Value (To) + Val);
            Set_Is_Static_Expression (Expr_Pos);
            Set_Etype (Expr_Pos, Etype (To));
            Set_Analyzed (Expr_Pos, Analyzed (To));

            if not Is_Enumeration_Type (Index_Typ) then
               Expr := Expr_Pos;

            --  If we are dealing with enumeration return
            --     Index_Typ'Val (Expr_Pos)

            else
               Expr :=
                 Make_Attribute_Reference
                   (Loc,
                    Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                    Attribute_Name => Name_Val,
                    Expressions    => New_List (Expr_Pos));
            end if;

            return Expr;
         end if;

         --  If we are here no constant folding possible

         if not Is_Enumeration_Type (Index_Base) then
            Expr :=
              Make_Op_Add (Loc,
                Left_Opnd  => Duplicate_Subexpr (To),
                Right_Opnd => Make_Integer_Literal (Loc, Val));

         --  If we are dealing with enumeration return
         --    Index_Typ'Val (Index_Typ'Pos (To) + Val)

         else
            To_Pos :=
              Make_Attribute_Reference
                (Loc,
                 Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                 Attribute_Name => Name_Pos,
                 Expressions    => New_List (Duplicate_Subexpr (To)));

            Expr_Pos :=
              Make_Op_Add (Loc,
                Left_Opnd  => To_Pos,
                Right_Opnd => Make_Integer_Literal (Loc, Val));

            Expr :=
              Make_Attribute_Reference
                (Loc,
                 Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                 Attribute_Name => Name_Val,
                 Expressions    => New_List (Expr_Pos));

            --  If the index type has a non standard representation, the
            --  attributes 'Val and 'Pos expand into function calls and the
            --  resulting expression is considered non-safe for reevaluation
            --  by the backend. Relocate it into a constant temporary in order
            --  to make it safe for reevaluation.

            if Has_Non_Standard_Rep (Etype (N)) then
               declare
                  Def_Id : Entity_Id;

               begin
                  Def_Id := Make_Temporary (Loc, 'R', Expr);
                  Set_Etype (Def_Id, Index_Typ);
                  Insert_Action (N,
                    Make_Object_Declaration (Loc,
                      Defining_Identifier => Def_Id,
                      Object_Definition   =>
                        New_Occurrence_Of (Index_Typ, Loc),
                      Constant_Present    => True,
                      Expression          => Relocate_Node (Expr)));

                  Expr := New_Occurrence_Of (Def_Id, Loc);
               end;
            end if;
         end if;

         return Expr;
      end Add;

      -----------------
      -- Check_Bound --
      -----------------

      procedure Check_Bound (BH : Node_Id; AH : in out Node_Id) is
         Val_BH : Uint;
         Val_AH : Uint;

         OK_BH : Boolean;
         OK_AH : Boolean;

      begin
         Get (Value => Val_BH, From => BH, OK => OK_BH);
         Get (Value => Val_AH, From => AH, OK => OK_AH);

         if OK_BH and then OK_AH and then Val_BH < Val_AH then
            Set_Raises_Constraint_Error (N);
            Error_Msg_Warn := SPARK_Mode /= On;
            Error_Msg_N ("upper bound out of range<<", AH);
            Error_Msg_N ("\Constraint_Error [<<", AH);

            --  You need to set AH to BH or else in the case of enumerations
            --  indexes we will not be able to resolve the aggregate bounds.

            AH := Duplicate_Subexpr (BH);
         end if;
      end Check_Bound;

      ------------------
      -- Check_Bounds --
      ------------------

      procedure Check_Bounds (L, H : Node_Id; AL, AH : Node_Id) is
         Val_L  : Uint;
         Val_H  : Uint;
         Val_AL : Uint;
         Val_AH : Uint;

         OK_L : Boolean;
         OK_H : Boolean;

         OK_AL : Boolean;
         OK_AH  : Boolean;
         pragma Warnings (Off, OK_AL);
         pragma Warnings (Off, OK_AH);

      begin
         if Raises_Constraint_Error (N)
           or else Dynamic_Or_Null_Range (AL, AH)
         then
            return;
         end if;

         Get (Value => Val_L, From => L, OK => OK_L);
         Get (Value => Val_H, From => H, OK => OK_H);

         Get (Value => Val_AL, From => AL, OK => OK_AL);
         Get (Value => Val_AH, From => AH, OK => OK_AH);

         if OK_L and then Val_L > Val_AL then
            Set_Raises_Constraint_Error (N);
            Error_Msg_Warn := SPARK_Mode /= On;
            Error_Msg_N ("lower bound of aggregate out of range<<", N);
            Error_Msg_N ("\Constraint_Error [<<", N);
         end if;

         if OK_H and then Val_H < Val_AH then
            Set_Raises_Constraint_Error (N);
            Error_Msg_Warn := SPARK_Mode /= On;
            Error_Msg_N ("upper bound of aggregate out of range<<", N);
            Error_Msg_N ("\Constraint_Error [<<", N);
         end if;
      end Check_Bounds;

      ------------------
      -- Check_Length --
      ------------------

      procedure Check_Length (L, H : Node_Id; Len : Uint) is
         Val_L  : Uint;
         Val_H  : Uint;

         OK_L  : Boolean;
         OK_H  : Boolean;

         Range_Len : Uint;

      begin
         if Raises_Constraint_Error (N) then
            return;
         end if;

         Get (Value => Val_L, From => L, OK => OK_L);
         Get (Value => Val_H, From => H, OK => OK_H);

         if not OK_L or else not OK_H then
            return;
         end if;

         --  If null range length is zero

         if Val_L > Val_H then
            Range_Len := Uint_0;
         else
            Range_Len := Val_H - Val_L + 1;
         end if;

         if Range_Len < Len then
            Set_Raises_Constraint_Error (N);
            Error_Msg_Warn := SPARK_Mode /= On;
            Error_Msg_N ("too many elements<<", N);
            Error_Msg_N ("\Constraint_Error [<<", N);
         end if;
      end Check_Length;

      ---------------------------
      -- Dynamic_Or_Null_Range --
      ---------------------------

      function Dynamic_Or_Null_Range (L, H : Node_Id) return Boolean is
         Val_L : Uint;
         Val_H : Uint;

         OK_L  : Boolean;
         OK_H  : Boolean;

      begin
         Get (Value => Val_L, From => L, OK => OK_L);
         Get (Value => Val_H, From => H, OK => OK_H);

         return not OK_L or else not OK_H
           or else not Is_OK_Static_Expression (L)
           or else not Is_OK_Static_Expression (H)
           or else Val_L > Val_H;
      end Dynamic_Or_Null_Range;

      ---------
      -- Get --
      ---------

      procedure Get (Value : out Uint; From : Node_Id; OK : out Boolean) is
      begin
         OK := True;

         if Compile_Time_Known_Value (From) then
            Value := Expr_Value (From);

         --  If expression From is something like Some_Type'Val (10) then
         --  Value = 10.

         elsif Nkind (From) = N_Attribute_Reference
           and then Attribute_Name (From) = Name_Val
           and then Compile_Time_Known_Value (First (Expressions (From)))
         then
            Value := Expr_Value (First (Expressions (From)));
         else
            Value := Uint_0;
            OK := False;
         end if;
      end Get;

      -------------------------------------------------
      -- Has_Null_Aggregate_Raising_Constraint_Error --
      -------------------------------------------------

      function Has_Null_Aggregate_Raising_Constraint_Error
        (Expr : Node_Id) return Boolean
      is
         function Process (N : Node_Id) return Traverse_Result;
         --  Process one node in search for generic formal type

         -------------
         -- Process --
         -------------

         function Process (N : Node_Id) return Traverse_Result is
         begin
            if Nkind (N) = N_Aggregate
              and then Is_Null_Aggregate (N)
              and then Raises_Constraint_Error (N)
            then
               return Abandon;
            end if;

            return OK;
         end Process;

         function Traverse is new Traverse_Func (Process);
         --  Traverse tree to look for null aggregates that will raise CE

      --  Start of processing for Has_Null_Aggregate_Raising_Constraint_Error

      begin
         return Traverse (Expr) = Abandon;
      end Has_Null_Aggregate_Raising_Constraint_Error;

      -----------------------
      -- Resolve_Aggr_Expr --
      -----------------------

      function Resolve_Aggr_Expr
        (Expr          : Node_Id;
         Iterated_Elmt : Boolean := False;
         Single_Elmt   : Boolean := True) return Boolean
      is
         Iterated_Expr  : constant Boolean := Iterated_Elmt or else Iterated;
         --  True if the Expr is in an iteration context, possibly nested

         Nxt_Ind        : constant Node_Id := Next_Index (Index);
         Nxt_Ind_Constr : constant Node_Id := Next_Index (Index_Constr);
         --  Index is the current index corresponding to the expression

         Resolution_OK  : Boolean := True;
         --  Set to False if resolution of the expression failed

      begin
         --  Defend against previous errors

         if Nkind (Expr) = N_Error
           or else Error_Posted (Expr)
         then
            return True;
         end if;

         --  If the array type against which we are resolving the aggregate
         --  has several dimensions, the expressions nested inside the
         --  aggregate must be further aggregates (or strings).

         if Present (Nxt_Ind) then
            if Nkind (Expr) /= N_Aggregate then

               --  A string literal can appear where a one-dimensional array
               --  of characters is expected. If the literal looks like an
               --  operator, it is still an operator symbol, which will be
               --  transformed into a string when analyzed.

               if Is_Character_Type (Ctyp)
                 and then No (Next_Index (Nxt_Ind))
                 and then Nkind (Expr) in N_String_Literal | N_Operator_Symbol
               then
                  --  A string literal used in a multidimensional array
                  --  aggregate in place of the final one-dimensional
                  --  aggregate must not be enclosed in parentheses.

                  if Paren_Count (Expr) /= 0 then
                     Error_Msg_N ("no parenthesis allowed here", Expr);
                  end if;

                  Make_String_Into_Aggregate (Expr);

               else
                  Error_Msg_N ("nested array aggregate expected", Expr);

                  --  If the expression is parenthesized, this may be
                  --  a missing component association for a 1-aggregate.

                  if Paren_Count (Expr) > 0 then
                     Error_Msg_N
                       ("\if single-component aggregate is intended, "
                        & "write e.g. (1 ='> ...)", Expr);
                  end if;

                  return Failure;
               end if;
            end if;

            --  Ada 2005 (AI-231): Propagate the type to the nested aggregate.
            --  Required to check the null-exclusion attribute (if present).
            --  This value may be overridden later on.

            Set_Etype (Expr, Etype (N));

            Resolution_OK :=
              Resolve_Array_Aggregate
                (Expr, Nxt_Ind, Nxt_Ind_Constr, Ctyp,
                 Iterated => Iterated_Expr, Others_Allowed => Others_Allowed);

            if Resolution_OK = Failure then
               return Failure;
            end if;

         else
            --  In an iterated context, preanalyze a copy of the expression to
            --  verify legality. We use a copy because the expression will be
            --  analyzed anew when the enclosing aggregate is expanded and the
            --  construct is rewritten as a loop with a new iteration variable.
            --  This does not apply to SPARK mode, where expansion is skipped.

            --  If the parent is a component association, we also temporarily
            --  point its Expression field to the copy, because analysis may
            --  expect this invariant to hold.

            if Iterated_Expr and then not GNATprove_Mode then
               declare
                  In_Assoc : constant Boolean :=
                    Nkind (Parent (Expr)) in N_Component_Association
                                           | N_Iterated_Component_Association;
                  New_Expr : constant Node_Id := Copy_Separate_Tree (Expr);

               begin
                  Set_Parent (New_Expr, Parent (Expr));
                  if In_Assoc then
                     Set_Expression (Parent (Expr), New_Expr);
                  end if;

                  Preanalyze_And_Resolve (New_Expr, Ctyp);
                  Check_Expr_OK_In_Limited_Aggregate (New_Expr);
                  Check_Expression_Dimensions (New_Expr, Ctyp);

                  if In_Assoc then
                     Set_Expression (Parent (Expr), Expr);
                  end if;
               end;

            --  If the expander is active and the choice may cover multiple
            --  components, then we cannot expand (see the spec of Sem), so
            --  we preanalyze the expression.

            elsif Expander_Active and then not Single_Elmt then
               Preanalyze_And_Resolve (Expr, Ctyp);
               Check_Expr_OK_In_Limited_Aggregate (Expr);
               Check_Expression_Dimensions (Expr, Ctyp);

               --  The range given by the choice may be empty, in which case we
               --  do not want spurious warnings about CE raised at run time.

               Remove_Warning_Messages (Expr);

            --  Otherwise, we perform a full analysis of the expression

            else
               Analyze_And_Resolve (Expr, Ctyp);
               Check_Expr_OK_In_Limited_Aggregate (Expr);
               Check_Expression_Dimensions (Expr, Ctyp);
               Check_Non_Static_Context (Expr);
               Check_Unset_Reference (Expr);
               Aggregate_Constraint_Checks (Expr, Ctyp);
            end if;
         end if;

         --  If an aggregate component has a type with predicates, an explicit
         --  predicate check must be applied, as for an assignment statement,
         --  because the aggregate might not be expanded into individual
         --  component assignments. If the expression covers several components
         --  the analysis and the predicate check take place later.

         if Has_Predicates (Ctyp)
           and then Analyzed (Expr)
         then
            Apply_Predicate_Check (Expr, Ctyp);
         end if;

         if Raises_Constraint_Error (Expr)
           and then (Nkind (Parent (Expr)) /= N_Component_Association
                      or else Is_Null_Aggregate (Expr))
         then
            Set_Raises_Constraint_Error (N);
         end if;

         --  If the expression has been marked as requiring a range check,
         --  then generate it here. It's a bit odd to be generating such
         --  checks in the analyzer, but harmless since Generate_Range_Check
         --  does nothing (other than making sure Do_Range_Check is set) if
         --  the expander is not active.

         if Do_Range_Check (Expr) then
            Generate_Range_Check (Expr, Ctyp, CE_Range_Check_Failed);
         end if;

         return Resolution_OK;
      end Resolve_Aggr_Expr;

      --------------------------------------------
      -- Resolve_Iterated_Component_Association --
      --------------------------------------------

      function Resolve_Iterated_Component_Association
        (N         : Node_Id;
         Index_Typ : Entity_Id) return Boolean
      is
         Loc  : constant Source_Ptr := Sloc (N);
         Id   : constant Entity_Id  := Defining_Identifier (N);
         Expr : constant Node_Id    := Expression (N);

         --  Local variables

         Choice         : Node_Id;
         Resolution_OK  : Boolean;
         Scop           : Entity_Id;

      --  Start of processing for Resolve_Iterated_Component_Association

      begin
         Error_Msg_Ada_2022_Feature ("iterated component", Loc);

         --  Create a scope in which to introduce an index, to make it visible
         --  for the analysis of component expression.

         Scop := New_Internal_Entity (E_Loop, Current_Scope, Loc, 'L');
         Set_Etype  (Scop, Standard_Void_Type);
         Set_Parent (Scop, Parent (N));
         Push_Scope (Scop);

         --  If there is iterator specification, then its preanalysis will make
         --  the index visible.

         if Present (Iterator_Specification (N)) then
            Preanalyze (Iterator_Specification (N));

         --  Otherwise, analyze discrete choices and make the index visible

         else
            --  Insert index name into current scope but don't decorate it yet,
            --  so that a premature usage of this name in discrete choices will
            --  be nicely diagnosed.

            Enter_Name (Id);

            Choice := First (Discrete_Choices (N));

            while Present (Choice) loop
               if Nkind (Choice) = N_Others_Choice then
                  Others_N := Choice;

               else
                  Analyze (Choice);

                  --  Choice can be a subtype name, a range, or an expression

                  if Is_Entity_Name (Choice)
                    and then Is_Type (Entity (Choice))
                    and then
                      Base_Type (Entity (Choice)) = Base_Type (Index_Typ)
                  then
                     null;

                  else
                     Analyze_And_Resolve (Choice, Index_Typ);
                  end if;
               end if;

               Next (Choice);
            end loop;

            --  Decorate the index variable

            Set_Etype (Id, Index_Typ);
            Mutate_Ekind (Id, E_Variable);
            Set_Is_Not_Self_Hidden (Id);
            Set_Scope (Id, Scop);
         end if;

         --  Analyze expression without expansion, to verify legality

         Resolution_OK := Resolve_Aggr_Expr (Expr, Iterated_Elmt => True);

         End_Scope;

         return Resolution_OK;
      end Resolve_Iterated_Component_Association;

      --------------
      -- Subtract --
      --------------

      function Subtract (Val : Uint; To : Node_Id) return Node_Id is
         Expr_Pos : Node_Id;
         Expr     : Node_Id;
         To_Pos   : Node_Id;

      begin
         if Raises_Constraint_Error (To) then
            return To;
         end if;

         --  First test if we can do constant folding

         if Compile_Time_Known_Value (To)
           or else Nkind (To) = N_Integer_Literal
         then
            Expr_Pos := Make_Integer_Literal (Loc, Expr_Value (To) - Val);
            Set_Is_Static_Expression (Expr_Pos);
            Set_Etype (Expr_Pos, Etype (To));
            Set_Analyzed (Expr_Pos, Analyzed (To));

            if not Is_Enumeration_Type (Index_Typ) then
               Expr := Expr_Pos;

            --  If we are dealing with enumeration return
            --     Index_Typ'Val (Expr_Pos)

            else
               Expr :=
                 Make_Attribute_Reference
                   (Loc,
                    Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                    Attribute_Name => Name_Val,
                    Expressions    => New_List (Expr_Pos));
            end if;

            return Expr;
         end if;

         --  If we are here no constant folding possible

         if not Is_Enumeration_Type (Index_Base) then
            Expr :=
              Make_Op_Subtract (Loc,
                Left_Opnd  => Duplicate_Subexpr (To),
                Right_Opnd => Make_Integer_Literal (Loc, Val));

         --  If we are dealing with enumeration return
         --    Index_Typ'Val (Index_Typ'Pos (To) - Val)

         else
            To_Pos :=
              Make_Attribute_Reference
                (Loc,
                 Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                 Attribute_Name => Name_Pos,
                 Expressions    => New_List (Duplicate_Subexpr (To)));

            Expr_Pos :=
              Make_Op_Subtract (Loc,
                Left_Opnd  => To_Pos,
                Right_Opnd => Make_Integer_Literal (Loc, Val));

            Expr :=
              Make_Attribute_Reference
                (Loc,
                 Prefix         => New_Occurrence_Of (Index_Typ, Loc),
                 Attribute_Name => Name_Val,
                 Expressions    => New_List (Expr_Pos));

            --  If the index type has a non standard representation, the
            --  attributes 'Val and 'Pos expand into function calls and the
            --  resulting expression is considered non-safe for reevaluation
            --  by the backend. Relocate it into a constant temporary in order
            --  to make it safe for reevaluation.

            if Has_Non_Standard_Rep (Etype (N)) then
               declare
                  Def_Id : Entity_Id;

               begin
                  Def_Id := Make_Temporary (Loc, 'R', Expr);
                  Set_Etype (Def_Id, Index_Typ);
                  Insert_Action (N,
                    Make_Object_Declaration (Loc,
                      Defining_Identifier => Def_Id,
                      Object_Definition   =>
                        New_Occurrence_Of (Index_Typ, Loc),
                      Constant_Present    => True,
                      Expression          => Relocate_Node (Expr)));

                  Expr := New_Occurrence_Of (Def_Id, Loc);
               end;
            end if;
         end if;

         return Expr;
      end Subtract;

      ----------------------------------------
      -- Warn_On_Null_Component_Association --
      ----------------------------------------

      procedure Warn_On_Null_Component_Association (Expr : Node_Id) is
         procedure Check_Case_Expr (N : Node_Id);
         --  Check if a case expression may initialize some component with a
         --  null value.

         procedure Check_Cond_Expr (N : Node_Id);
         --  Check if a conditional expression may initialize some component
         --  with a null value.

         procedure Check_Expr (Expr : Node_Id);
         --  Check if an expression may initialize some component with a
         --  null value.

         procedure Warn_On_Null_Expression_And_Rewrite (Null_Expr : Node_Id);
         --  Report warning on known null expression and replace the expression
         --  by a raise constraint error node.

         ---------------------
         -- Check_Case_Expr --
         ---------------------

         procedure Check_Case_Expr (N : Node_Id) is
            Alt_Node : Node_Id := First (Alternatives (N));

         begin
            while Present (Alt_Node) loop
               Check_Expr (Expression (Alt_Node));
               Next (Alt_Node);
            end loop;
         end Check_Case_Expr;

         ---------------------
         -- Check_Cond_Expr --
         ---------------------

         procedure Check_Cond_Expr (N : Node_Id) is
            If_Expr   : Node_Id := N;
            Then_Expr : Node_Id;
            Else_Expr : Node_Id;

         begin
            Then_Expr := Next (First (Expressions (If_Expr)));
            Else_Expr := Next (Then_Expr);

            Check_Expr (Then_Expr);

            --  Process elsif parts (if any)

            while Nkind (Else_Expr) = N_If_Expression loop
               If_Expr   := Else_Expr;
               Then_Expr := Next (First (Expressions (If_Expr)));
               Else_Expr := Next (Then_Expr);

               Check_Expr (Then_Expr);
            end loop;

            if Known_Null (Else_Expr) then
               Warn_On_Null_Expression_And_Rewrite (Else_Expr);
            end if;
         end Check_Cond_Expr;

         ----------------
         -- Check_Expr --
         ----------------

         procedure Check_Expr (Expr : Node_Id) is
         begin
            if Known_Null (Expr) then
               Warn_On_Null_Expression_And_Rewrite (Expr);

            elsif Nkind (Expr) = N_If_Expression then
               Check_Cond_Expr (Expr);

            elsif Nkind (Expr) = N_Case_Expression then
               Check_Case_Expr (Expr);
            end if;
         end Check_Expr;

         -----------------------------------------
         -- Warn_On_Null_Expression_And_Rewrite --
         -----------------------------------------

         procedure Warn_On_Null_Expression_And_Rewrite (Null_Expr : Node_Id) is
         begin
            Error_Msg_N
              ("(Ada 2005) NULL not allowed in null-excluding component??",
               Null_Expr);
            Error_Msg_N
              ("\Constraint_Error might be raised at run time??", Null_Expr);

            --  We cannot use Apply_Compile_Time_Constraint_Error because in
            --  some cases the components are rewritten and the runtime error
            --  would be missed.

            Rewrite (Null_Expr,
              Make_Raise_Constraint_Error (Sloc (Null_Expr),
                Reason => CE_Access_Check_Failed));

            Set_Etype    (Null_Expr, Ctyp);
            Set_Analyzed (Null_Expr);
         end Warn_On_Null_Expression_And_Rewrite;

      --  Start of processing for Warn_On_Null_Component_Association

      begin
         pragma Assert (Can_Never_Be_Null (Ctyp));

         case Nkind (Expr) is
            when N_If_Expression =>
               Check_Cond_Expr (Expr);

            when N_Case_Expression =>
               Check_Case_Expr (Expr);

            when others =>
               pragma Assert (False);
               null;
         end case;
      end Warn_On_Null_Component_Association;

      --  Local variables

      Assoc   : Node_Id;
      Choice  : Node_Id;
      Expr    : Node_Id;
      Discard : Node_Id;

      Aggr_Low  : Node_Id := Empty;
      Aggr_High : Node_Id := Empty;
      --  The actual low and high bounds of this sub-aggregate

      Case_Table_Size : Nat;
      --  Contains the size of the case table needed to sort aggregate choices

      Choices_Low  : Node_Id := Empty;
      Choices_High : Node_Id := Empty;
      --  The lowest and highest discrete choices values for a named aggregate

      Delete_Choice : Boolean;
      --  Used when replacing a subtype choice with predicate by a list

      Has_Iterator_Specifications : Boolean := False;
      --  Flag to indicate that all named associations are iterated component
      --  associations with iterator specifications, in which case the
      --  expansion will create two loops: one to evaluate the size and one
      --  to generate the elements (4.3.3 (20.2/5)).

      Nb_Elements : Uint := Uint_0;
      --  The number of elements in a positional aggregate

      Nb_Discrete_Choices : Nat := 0;
      --  The overall number of discrete choices (not counting others choice)

   --  Start of processing for Resolve_Array_Aggregate

   begin
      --  Ignore junk empty aggregate resulting from parser error

      if No (Expressions (N))
        and then No (Component_Associations (N))
        and then not Null_Record_Present (N)
      then
         return Failure;
      end if;

      --  Disable the warning for GNAT Mode to allow for easier transition.

      --  We don't warn about obsolescent usage of parentheses in generic
      --  instances for two reasons:
      --
      --  1. An equivalent warning has been emitted in the corresponding
      --     definition.
      --  2. In cases where a generic definition specifies a version older than
      --     Ada 2022 through a pragma and rightfully uses parentheses for
      --     an array aggregate, an incorrect warning would be raised in
      --     instances of that generic that are in Ada 2022 or later if we
      --     didn't filter out the instance case.

      if Ada_Version_Explicit >= Ada_2022
        and then Warn_On_Obsolescent_Feature
        and then not GNAT_Mode
        and then not Is_Homogeneous_Aggregate (N)
        and then Is_Parenthesis_Aggregate (N)
        and then Nkind (Parent (N)) /= N_Qualified_Expression
        and then Comes_From_Source (N)
        and then not In_Instance
      then
         Error_Msg_N
           ("?j?array aggregate using () is an" &
              " obsolescent syntax, use '['] instead", N);
      end if;

      --  STEP 1: make sure the aggregate is correctly formatted

      if Is_Null_Aggregate (N) then
         null;

      elsif Present (Component_Associations (N)) then
         Assoc := First (Component_Associations (N));

         --  Loop over associations to identify any iterated associations that
         --  need to be converted from the form with a Defining_Identifer and
         --  Discrete_Choices list to the form with an Iterator_Specification.

         if Nkind (Assoc) = N_Iterated_Component_Association then
            while Present (Assoc) loop
               if Nkind (Assoc) = N_Iterated_Component_Association
                 and then No (Iterator_Specification (Assoc))
               then
                  declare
                     Choice : constant Node_Id :=
                       First (Discrete_Choices (Assoc));
                     Copy   : Node_Id;
                  begin

                     --  A copy of Choice is made before it's analyzed,
                     --  to preserve prefixed calls in their original form,
                     --  because otherwise the analysis of Choice can transform
                     --  such calls to normal form, and the later analysis of
                     --  the iterator_specification created below may trigger
                     --  an error on the call (in the case where the function
                     --  is not directly visible).

                     Copy := Copy_Separate_Tree (Choice);

                     --  This is an association with a Defining_Identifier and
                     --  Discrete_Choice_List, but if the latter has a single
                     --  choice denoting an object (including a function call)
                     --  of an iterator type, then it's a stand-in for an
                     --  Iterator_Specification, and so we transform the
                     --  association accordingly.

                     if No (Next (Choice)) then
                        Analyze (Choice);

                        if Is_Object_Reference (Choice)
                          and then Is_Iterator (Etype (Choice))
                        then
                           Set_Iterator_Specification
                             (Assoc,
                              Make_Iterator_Specification (Sloc (N),
                                Defining_Identifier =>
                                  Relocate_Node (Defining_Identifier (Assoc)),
                                Name                => Copy,
                                Reverse_Present     => Reverse_Present (Assoc),
                                Iterator_Filter     => Empty,
                                Subtype_Indication  => Empty));

                           Set_Defining_Identifier (Assoc, Empty);
                           Set_Discrete_Choices (Assoc, No_List);
                        end if;
                     end if;
                  end;
               end if;

               Next (Assoc);
            end loop;
         end if;

         --  Verify that all or none of the component associations
         --  include an iterator specification.

         Assoc := First (Component_Associations (N));
         if Nkind (Assoc) = N_Iterated_Component_Association
           and then Present (Iterator_Specification (Assoc))
         then
            if Number_Dimensions (Etype (N)) /= 1 then
               Error_Msg_N ("iterated_component_association with an" &
                            " iterator_specification not allowed for" &
                            " multidimensional array aggregate",
                            Assoc);
               return Failure;
            end if;

            --  All other component associations must have an iterator spec.

            Next (Assoc);
            while Present (Assoc) loop
               if Nkind (Assoc) /= N_Iterated_Component_Association
                 or else No (Iterator_Specification (Assoc))
               then
                  Error_Msg_N ("mixed iterated component association"
                   & " (RM 4.3.3 (17.1/5))",
                      Assoc);
                  return Failure;
               end if;

               Next (Assoc);
            end loop;

            Has_Iterator_Specifications := True;

         else
            --  or none of them do.

            Next (Assoc);
            while Present (Assoc) loop
               if Nkind (Assoc) = N_Iterated_Component_Association
                 and then Present (Iterator_Specification (Assoc))
               then
                  Error_Msg_N ("mixed iterated component association"
                    & " (RM 4.3.3 (17.1/5))",
                      Assoc);
                  return Failure;
               end if;

               Next (Assoc);
            end loop;

         end if;

         Assoc := First (Component_Associations (N));
         while Present (Assoc) loop
            if Nkind (Assoc) = N_Iterated_Component_Association then
               if not Resolve_Iterated_Component_Association
                        (Assoc, Index_Typ)
               then
                  return Failure;
               end if;

            elsif Nkind (Assoc) /= N_Component_Association then
               Error_Msg_N
                 ("invalid component association for aggregate", Assoc);
               return Failure;
            end if;

            Choice := First (Choice_List (Assoc));
            Delete_Choice := False;
            while Present (Choice) loop
               if Nkind (Choice) = N_Others_Choice then
                  Others_N := Choice;

                  if Choice /= First (Choice_List (Assoc))
                    or else Present (Next (Choice))
                  then
                     Error_Msg_N
                       ("OTHERS must appear alone in a choice list", Choice);
                     return Failure;
                  end if;

                  if Present (Next (Assoc)) then
                     Error_Msg_N
                       ("OTHERS must appear last in an aggregate", Choice);
                     return Failure;
                  end if;

                  if Ada_Version = Ada_83
                    and then Assoc /= First (Component_Associations (N))
                    and then Nkind (Parent (N)) in
                               N_Assignment_Statement | N_Object_Declaration
                  then
                     Error_Msg_N
                       ("(Ada 83) illegal context for OTHERS choice", N);
                  end if;

               elsif Is_Entity_Name (Choice) then
                  Analyze (Choice);

                  declare
                     E      : constant Entity_Id := Entity (Choice);
                     New_Cs : List_Id;
                     P      : Node_Id;
                     C      : Node_Id;

                  begin
                     if Is_Type (E) and then Has_Predicates (E) then
                        Freeze_Before (N, E);

                        if Has_Dynamic_Predicate_Aspect (E)
                          or else Has_Ghost_Predicate_Aspect (E)
                        then
                           Error_Msg_NE
                             ("subtype& has non-static predicate, not allowed "
                              & "in aggregate choice", Choice, E);

                        elsif not Is_OK_Static_Subtype (E) then
                           Error_Msg_NE
                             ("non-static subtype& has predicate, not allowed "
                              & "in aggregate choice", Choice, E);
                        end if;

                        --  If the subtype has a static predicate, replace the
                        --  original choice with the list of individual values
                        --  covered by the predicate.
                        --  This should be deferred to expansion time ???

                        if Present (Static_Discrete_Predicate (E)) then
                           Delete_Choice := True;

                           New_Cs := New_List;
                           P := First (Static_Discrete_Predicate (E));
                           while Present (P) loop
                              C := New_Copy (P);
                              Set_Sloc (C, Sloc (Choice));
                              Append_To (New_Cs, C);
                              Next (P);
                           end loop;

                           Insert_List_After (Choice, New_Cs);
                        end if;
                     end if;
                  end;
               end if;

               Nb_Choices := Nb_Choices + 1;

               declare
                  C : constant Node_Id := Choice;

               begin
                  Next (Choice);

                  if Delete_Choice then
                     Remove (C);
                     Nb_Choices := Nb_Choices - 1;
                     Delete_Choice := False;
                  end if;
               end;
            end loop;

            Next (Assoc);
         end loop;
      end if;

      --  At this point we know that the others choice, if present, is by
      --  itself and appears last in the aggregate. Check if we have mixed
      --  positional and discrete associations (other than the others choice).

      if Present (Expressions (N))
        and then (Nb_Choices > 1
                   or else (Nb_Choices = 1 and then No (Others_N)))
      then
         Error_Msg_N
           ("cannot mix named and positional associations in array aggregate",
            First (Choice_List (First (Component_Associations (N)))));
         return Failure;
      end if;

      --  Test for the validity of an others choice if present

      if Present (Others_N) and then not Others_Allowed then
         Error_Msg_N ("OTHERS choice not allowed here", Others_N);
         Error_Msg_N ("\qualify the aggregate with a constrained subtype "
                      & "to provide bounds for it", Others_N);
         return Failure;
      end if;

      --  Protect against cascaded errors

      if Etype (Index_Typ) = Any_Type then
         return Failure;
      end if;

      --  STEP 2: Process named components

      if No (Expressions (N)) then
         if Present (Others_N) then
            Case_Table_Size := Nb_Choices - 1;
         else
            Case_Table_Size := Nb_Choices;
         end if;

         Step_2 : declare
            function Empty_Range (A : Node_Id) return Boolean;
            --  If an association covers an empty range, some warnings on the
            --  expression of the association can be disabled.

            -----------------
            -- Empty_Range --
            -----------------

            function Empty_Range (A : Node_Id) return Boolean is
               R : constant Node_Id := First (Choice_List (A));

            begin
               return No (Next (R))
                 and then Nkind (R) = N_Range
                 and then Compile_Time_Compare
                            (Low_Bound (R), High_Bound (R), False) = GT;
            end Empty_Range;

            --  Local variables

            Low  : Node_Id;
            High : Node_Id;
            --  Denote the lowest and highest values in an aggregate choice

            S_Low  : Node_Id := Empty;
            S_High : Node_Id := Empty;
            --  if a choice in an aggregate is a subtype indication these
            --  denote the lowest and highest values of the subtype

            Table : Case_Table_Type (1 .. Case_Table_Size);
            --  Used to sort all the different choice values

            Single_Choice : Boolean;
            --  Set to true every time there is a single discrete choice in a
            --  discrete association

            Prev_Nb_Discrete_Choices : Nat;
            --  Used to keep track of the number of discrete choices in the
            --  current association.

            Errors_Posted_On_Choices : Boolean := False;
            --  Keeps track of whether any choices have semantic errors

         --  Start of processing for Step_2

         begin
            --  STEP 2 (A): Check discrete choices validity
            --  No need if this is an element iteration.

            Assoc := First (Component_Associations (N));
            while Present (Assoc)
              and then Present (Choice_List (Assoc))
            loop
               Prev_Nb_Discrete_Choices := Nb_Discrete_Choices;
               Choice := First (Choice_List (Assoc));

               loop
                  Analyze (Choice);

                  if Nkind (Choice) = N_Others_Choice then
                     Single_Choice := False;
                     exit;

                  --  Test for subtype mark without constraint

                  elsif Is_Entity_Name (Choice) and then
                    Is_Type (Entity (Choice))
                  then
                     if Base_Type (Entity (Choice)) /= Index_Base then
                        Error_Msg_N
                          ("invalid subtype mark in aggregate choice",
                           Choice);
                        return Failure;
                     end if;

                  --  Case of subtype indication

                  elsif Nkind (Choice) = N_Subtype_Indication then
                     Resolve_Discrete_Subtype_Indication (Choice, Index_Base);

                     if Has_Dynamic_Predicate_Aspect
                          (Entity (Subtype_Mark (Choice)))
                       or else Has_Ghost_Predicate_Aspect
                                 (Entity (Subtype_Mark (Choice)))
                     then
                        Error_Msg_NE
                          ("subtype& has non-static predicate, "
                           & "not allowed in aggregate choice",
                           Choice, Entity (Subtype_Mark (Choice)));
                     end if;

                     --  Does the subtype indication evaluation raise CE?

                     Get_Index_Bounds (Subtype_Mark (Choice), S_Low, S_High);
                     Get_Index_Bounds (Choice, Low, High);
                     Check_Bounds (S_Low, S_High, Low, High);

                  --  Case of range or expression

                  else
                     Resolve (Choice, Index_Base);
                     Check_Unset_Reference (Choice);
                     Check_Non_Static_Context (Choice);

                     --  If semantic errors were posted on the choice, then
                     --  record that for possible early return from later
                     --  processing (see handling of enumeration choices).

                     if Error_Posted (Choice) then
                        Errors_Posted_On_Choices := True;
                     end if;

                     --  Do not range check a choice. This check is redundant
                     --  since this test is already done when we check that the
                     --  bounds of the array aggregate are within range.

                     Set_Do_Range_Check (Choice, False);
                  end if;

                  --  If we could not resolve the discrete choice stop here

                  if Etype (Choice) = Any_Type then
                     return Failure;

                  --  If the discrete choice raises CE get its original bounds

                  elsif Nkind (Choice) = N_Raise_Constraint_Error then
                     Set_Raises_Constraint_Error (N);
                     Get_Index_Bounds (Original_Node (Choice), Low, High);

                  --  Otherwise get its bounds as usual

                  else
                     Get_Index_Bounds (Choice, Low, High);
                  end if;

                  if Dynamic_Or_Null_Range (Low, High)
                    or else (Nkind (Choice) = N_Subtype_Indication
                             and then Dynamic_Or_Null_Range (S_Low, S_High))
                  then
                     if Nb_Choices /= 1 then
                        Error_Msg_N
                          ("dynamic or empty choice in aggregate "
                           & "must be the only choice", Choice);
                        return Failure;
                     elsif Number_Dimensions (Etype (N)) > 1 then
                        declare
                           function Check_Bound_Subexpression
                             (Exp : Node_Id) return Traverse_Result;
                           --  A bound expression for a subaggregate of an
                           --  array aggregate is not permitted to reference
                           --  a loop iteration variable defined in an earlier
                           --  dimension of the same enclosing aggregate, as
                           --  in (for X in 1 .. 3 => (1 .. X + 2 => ...)) .
                           --  Always returns OK.

                           --------------------------------
                           --  Check_Bound_Subexpression --
                           --------------------------------

                           function Check_Bound_Subexpression
                             (Exp : Node_Id) return Traverse_Result
                           is
                              Scope_Parent : Node_Id;
                           begin
                              if Nkind (Exp) /= N_Identifier
                                or else No (Entity (Exp))
                                or else No (Scope (Entity (Exp)))
                                or else Ekind (Scope (Entity (Exp))) /= E_Loop
                              then
                                 return OK;
                              end if;

                              Scope_Parent := Parent (Scope (Entity (Exp)));

                              if Nkind (Scope_Parent) = N_Aggregate

                                 --  We want to know whether the aggregate
                                 --  where this loop var is defined is
                                 --  "the same" aggregate as N, where "the
                                 --  same" means looking through subaggregates.
                                 --  To do this, we compare Etypes of the two.
                                 --
                                 --  ??? There may be very obscure cases
                                 --  involving allocators where this is too
                                 --  strict and will generate a spurious error.

                                 and then Etype (Scope_Parent) = Etype (N)
                              then
                                 Error_Msg_N ("bound expression for a "
                                   & "subaggregate of an array aggregate must "
                                   & "not refer to an index parameter of an "
                                   & "earlier dimension", Exp);
                              end if;

                              return OK;
                           end Check_Bound_Subexpression;

                           procedure Check_Bound_Expression is new
                             Traverse_Proc (Check_Bound_Subexpression);
                        begin
                           Check_Bound_Expression (Low);
                           Check_Bound_Expression (High);
                        end;
                     end if;
                  end if;

                  if not (All_Composite_Constraints_Static (Low)
                            and then All_Composite_Constraints_Static (High)
                            and then All_Composite_Constraints_Static (S_Low)
                            and then All_Composite_Constraints_Static (S_High))
                  then
                     Check_Restriction (No_Dynamic_Sized_Objects, Choice);
                  end if;

                  Nb_Discrete_Choices := Nb_Discrete_Choices + 1;
                  Table (Nb_Discrete_Choices).Lo := Low;
                  Table (Nb_Discrete_Choices).Hi := High;
                  Table (Nb_Discrete_Choices).Choice := Choice;

                  Next (Choice);

                  if No (Choice) then

                     --  Check if we have a single discrete choice and whether
                     --  this discrete choice specifies a single value.

                     Single_Choice :=
                       Nb_Discrete_Choices = Prev_Nb_Discrete_Choices + 1
                         and then Low = High;

                     exit;
                  end if;
               end loop;

               --  Ada 2005 (AI-231)

               if Ada_Version >= Ada_2005
                 and then not Empty_Range (Assoc)
               then
                  if Known_Null (Expression (Assoc)) then
                     Check_Can_Never_Be_Null (Etype (N), Expression (Assoc));

                  --  Report warning on iterated component association that may
                  --  initialize some component of an array of null-excluding
                  --  access type components with a null value. For example:

                  --     type AList is array (...) of not null access Integer;
                  --     L : AList :=
                  --          [for J in A'Range =>
                  --            (if Func (J) = 0 then A(J)'Access else Null)];

                  elsif Ada_Version >= Ada_2022
                    and then Can_Never_Be_Null (Ctyp)
                    and then Nkind (Assoc) = N_Iterated_Component_Association
                    and then Nkind (Expression (Assoc)) in N_If_Expression
                                                         | N_Case_Expression
                  then
                     Warn_On_Null_Component_Association (Expression (Assoc));
                  end if;
               end if;

               --  Ada 2005 (AI-287): In case of default initialized component
               --  we delay the resolution to the expansion phase.

               if Box_Present (Assoc) then

                  --  Ada 2005 (AI-287): In case of default initialization of
                  --  a component, the expander will generate calls to the
                  --  corresponding initialization subprogram. Check that we
                  --  have a single dimension.

                  if Present (Next_Index (Index)) then
                     Error_Msg_N ("nested array aggregate expected", Assoc);
                     return Failure;
                  end if;

               --  ??? Checks for dynamically tagged expressions below will
               --  be only applied to iterated_component_association after
               --  expansion; in particular, errors might not be reported when
               --  -gnatc switch is used.

               elsif Nkind (Assoc) = N_Iterated_Component_Association then
                  null;   --  handled above, in a loop context

               elsif not Resolve_Aggr_Expr
                           (Expression (Assoc), Single_Elmt => Single_Choice)
               then
                  return Failure;

               --  Check incorrect use of dynamically tagged expression

               --  We differentiate here two cases because the expression may
               --  not be decorated. For example, the analysis and resolution
               --  of the expression associated with the others choice will be
               --  done later with the full aggregate. In such case we
               --  duplicate the expression tree to analyze the copy and
               --  perform the required check.

               elsif No (Etype (Expression (Assoc))) then
                  declare
                     Expr : constant Node_Id :=
                              New_Copy_Tree (Expression (Assoc));

                  begin
                     --  Preanalyze the expression, making sure it is properly
                     --  attached to the tree before we do the analysis.

                     Set_Parent (Expr, Parent (Expression (Assoc)));
                     Preanalyze (Expr);

                     --  If the expression is a literal, propagate this info
                     --  to the expression in the association, to enable some
                     --  optimizations downstream.

                     if Is_Entity_Name (Expr)
                       and then Present (Entity (Expr))
                       and then Ekind (Entity (Expr)) = E_Enumeration_Literal
                     then
                        Preanalyze_And_Resolve (Expression (Assoc), Ctyp);
                     end if;

                     --  Skip tagged checking for mutably tagged CW equivalent
                     --  types.

                     if Is_Tagged_Type (Etype (Expr))
                       and then Is_Class_Wide_Equivalent_Type (Ctyp)
                     then
                        null;

                     --  Otherwise perform the dynamic tag check

                     elsif Is_Tagged_Type (Etype (Expr)) then
                        Check_Dynamically_Tagged_Expression
                          (Expr => Expr,
                           Typ  => Ctyp,
                           Related_Nod => N);
                     end if;
                  end;

               elsif Is_Tagged_Type (Etype (Expression (Assoc))) then
                  Check_Dynamically_Tagged_Expression
                    (Expr        => Expression (Assoc),
                     Typ         => Ctyp,
                     Related_Nod => N);
               end if;

               --  Propagate the attribute Raises_CE when it was reported on a
               --  null aggregate. This will cause replacing the aggregate by a
               --  raise CE node; it is not done in other cases to avoid such
               --  replacement and report complementary warnings when the
               --  expression is resolved.

               if Present (Expression (Assoc))
                 and then Has_Null_Aggregate_Raising_Constraint_Error
                            (Expression (Assoc))
               then
                  Set_Raises_Constraint_Error (N);
               end if;

               Next (Assoc);
            end loop;

            --  If aggregate contains more than one choice then these must be
            --  static. Check for duplicate and missing values.

            --  Note: there is duplicated code here wrt Check_Choice_Set in
            --  the body of Sem_Case, and it is possible we could just reuse
            --  that procedure. To be checked ???

            if Nb_Discrete_Choices > 1 then
               Check_Choices : declare
                  Choice : Node_Id;
                  --  Location of choice for messages

                  Hi_Val : Uint;
                  Lo_Val : Uint;
                  --  High end of one range and Low end of the next. Should be
                  --  contiguous if there is no hole in the list of values.

                  Lo_Dup : Uint;
                  Hi_Dup : Uint;
                  --  End points of duplicated range

                  Missing_Or_Duplicates : Boolean := False;
                  --  Set True if missing or duplicate choices found

                  procedure Output_Bad_Choices (Lo, Hi : Uint; C : Node_Id);
                  --  Output continuation message with a representation of the
                  --  bounds (just Lo if Lo = Hi, else Lo .. Hi). C is the
                  --  choice node where the message is to be posted.

                  ------------------------
                  -- Output_Bad_Choices --
                  ------------------------

                  procedure Output_Bad_Choices (Lo, Hi : Uint; C : Node_Id) is
                  begin
                     --  Enumeration type case

                     if Is_Enumeration_Type (Index_Typ) then
                        Error_Msg_Name_1 :=
                          Chars (Get_Enum_Lit_From_Pos (Index_Typ, Lo, Loc));
                        Error_Msg_Name_2 :=
                          Chars (Get_Enum_Lit_From_Pos (Index_Typ, Hi, Loc));

                        if Lo = Hi then
                           Error_Msg_N ("\\  %!", C);
                        else
                           Error_Msg_N ("\\  % .. %!", C);
                        end if;

                        --  Integer types case

                     else
                        Error_Msg_Uint_1 := Lo;
                        Error_Msg_Uint_2 := Hi;

                        if Lo = Hi then
                           Error_Msg_N ("\\  ^!", C);
                        else
                           Error_Msg_N ("\\  ^ .. ^!", C);
                        end if;
                     end if;
                  end Output_Bad_Choices;

               --  Start of processing for Check_Choices

               begin
                  Sort_Case_Table (Table);

                  --  First we do a quick linear loop to find out if we have
                  --  any duplicates or missing entries (usually we have a
                  --  legal aggregate, so this will get us out quickly).

                  for J in 1 .. Nb_Discrete_Choices - 1 loop
                     Hi_Val := Expr_Value (Table (J).Hi);
                     Lo_Val := Expr_Value (Table (J + 1).Lo);

                     if Lo_Val <= Hi_Val
                       or else (Lo_Val > Hi_Val + 1
                                 and then No (Others_N))
                     then
                        Missing_Or_Duplicates := True;
                        exit;
                     end if;
                  end loop;

                  --  If we have missing or duplicate entries, first fill in
                  --  the Highest entries to make life easier in the following
                  --  loops to detect bad entries.

                  if Missing_Or_Duplicates then
                     Table (1).Highest := Expr_Value (Table (1).Hi);

                     for J in 2 .. Nb_Discrete_Choices loop
                        Table (J).Highest :=
                          UI_Max
                            (Table (J - 1).Highest, Expr_Value (Table (J).Hi));
                     end loop;

                     --  Loop through table entries to find duplicate indexes

                     for J in 2 .. Nb_Discrete_Choices loop
                        Lo_Val := Expr_Value (Table (J).Lo);
                        Hi_Val := Expr_Value (Table (J).Hi);

                        --  Case where we have duplicates (the lower bound of
                        --  this choice is less than or equal to the highest
                        --  high bound found so far).

                        if Lo_Val <= Table (J - 1).Highest then

                           --  We move backwards looking for duplicates. We can
                           --  abandon this loop as soon as we reach a choice
                           --  highest value that is less than Lo_Val.

                           for K in reverse 1 .. J - 1 loop
                              exit when Table (K).Highest < Lo_Val;

                              --  Here we may have duplicates between entries
                              --  for K and J. Get range of duplicates.

                              Lo_Dup :=
                                UI_Max (Lo_Val, Expr_Value (Table (K).Lo));
                              Hi_Dup :=
                                UI_Min (Hi_Val, Expr_Value (Table (K).Hi));

                              --  Nothing to do if duplicate range is null

                              if Lo_Dup > Hi_Dup then
                                 null;

                              --  Otherwise place proper message

                              else
                                 --  We place message on later choice, with a
                                 --  line reference to the earlier choice.

                                 if Sloc (Table (J).Choice) <
                                   Sloc (Table (K).Choice)
                                 then
                                    Choice := Table (K).Choice;
                                    Error_Msg_Sloc := Sloc (Table (J).Choice);
                                 else
                                    Choice := Table (J).Choice;
                                    Error_Msg_Sloc := Sloc (Table (K).Choice);
                                 end if;

                                 if Lo_Dup = Hi_Dup then
                                    Error_Msg_N
                                      ("index value in array aggregate "
                                       & "duplicates the one given#!", Choice);
                                 else
                                    Error_Msg_N
                                      ("index values in array aggregate "
                                       & "duplicate those given#!", Choice);
                                 end if;

                                 Output_Bad_Choices (Lo_Dup, Hi_Dup, Choice);
                              end if;
                           end loop;
                        end if;
                     end loop;

                     --  Loop through entries in table to find missing indexes.
                     --  Not needed if others, since missing impossible.

                     if No (Others_N) then
                        for J in 2 .. Nb_Discrete_Choices loop
                           Lo_Val := Expr_Value (Table (J).Lo);
                           Hi_Val := Table (J - 1).Highest;

                           if Lo_Val > Hi_Val + 1 then

                              declare
                                 Error_Node : Node_Id;

                              begin
                                 --  If the choice is the bound of a range in
                                 --  a subtype indication, it is not in the
                                 --  source lists for the aggregate itself, so
                                 --  post the error on the aggregate. Otherwise
                                 --  post it on choice itself.

                                 Choice := Table (J).Choice;

                                 if Is_List_Member (Choice) then
                                    Error_Node := Choice;
                                 else
                                    Error_Node := N;
                                 end if;

                                 if Hi_Val + 1 = Lo_Val - 1 then
                                    Error_Msg_N
                                      ("missing index value "
                                       & "in array aggregate!", Error_Node);
                                 else
                                    Error_Msg_N
                                      ("missing index values "
                                       & "in array aggregate!", Error_Node);
                                 end if;

                                 Output_Bad_Choices
                                   (Hi_Val + 1, Lo_Val - 1, Error_Node);
                              end;
                           end if;
                        end loop;
                     end if;

                     --  If either missing or duplicate values, return failure

                     Set_Etype (N, Any_Composite);
                     return Failure;
                  end if;
               end Check_Choices;
            end if;

            if Has_Iterator_Specifications then
               --  Bounds will be determined dynamically.

               return Success;
            end if;

            --  STEP 2 (B): Compute aggregate bounds and min/max choices values

            if Nb_Discrete_Choices > 0 then
               Choices_Low  := Table (1).Lo;
               Choices_High := Table (Nb_Discrete_Choices).Hi;
            end if;

            --  If Others is present, then bounds of aggregate come from the
            --  index constraint (not the choices in the aggregate itself).

            if Present (Others_N) then
               Get_Index_Bounds (Index_Constr, Aggr_Low, Aggr_High);

               --  Abandon processing if either bound is already signalled as
               --  an error (prevents junk cascaded messages and blow ups).

               if Nkind (Aggr_Low) = N_Error
                    or else
                  Nkind (Aggr_High) = N_Error
               then
                  return False;
               end if;

            --  No others clause present

            else
               --  Special processing if others allowed and not present. In
               --  this case, the bounds of the aggregate come from the
               --  choices (RM 4.3.3 (27)).

               if Others_Allowed then
                  Get_Index_Bounds (Index_Constr, Aggr_Low, Aggr_High);

                  --  Abandon processing if either bound is already signalled
                  --  as an error (stop junk cascaded messages and blow ups).

                  if Nkind (Aggr_Low) = N_Error
                       or else
                     Nkind (Aggr_High) = N_Error
                  then
                     return False;
                  end if;

                  --  If there is an applicable index constraint and others is
                  --  not present, then sliding is allowed and only a length
                  --  check will be performed. However, additional warnings are
                  --  useful if the index type is an enumeration type, as
                  --  sliding is dubious in this case. We emit two kinds of
                  --  warnings:
                  --
                  --    1. If the length is wrong then there are missing
                  --       components; we issue appropriate warnings about
                  --       these missing components. They are only warnings,
                  --       since the aggregate is fine, it's just the wrong
                  --       length. We skip this check for standard character
                  --       types (since there are no literals and it is too
                  --       much trouble to concoct them), and also if any of
                  --       the bounds have values that are not known at compile
                  --       time.
                  --
                  --    2. If the length is right but the bounds do not match,
                  --       we issue a warning, as we consider sliding dubious
                  --       when the index type is an enumeration type.

                  if Nkind (Index) = N_Range
                    and then Is_Enumeration_Type (Etype (Index))
                    and then not Is_Standard_Character_Type (Etype (Index))
                    and then Compile_Time_Known_Value (Aggr_Low)
                    and then Compile_Time_Known_Value (Aggr_High)
                    and then Compile_Time_Known_Value (Choices_Low)
                    and then Compile_Time_Known_Value (Choices_High)
                  then
                     --  If any of the expressions or range bounds in choices
                     --  have semantic errors, then do not attempt further
                     --  resolution, to prevent cascaded errors.

                     if Errors_Posted_On_Choices then
                        return Failure;
                     end if;

                     declare
                        ALo : constant Node_Id := Expr_Value_E (Aggr_Low);
                        AHi : constant Node_Id := Expr_Value_E (Aggr_High);
                        CLo : constant Node_Id := Expr_Value_E (Choices_Low);
                        CHi : constant Node_Id := Expr_Value_E (Choices_High);

                        Ent : Entity_Id;

                     begin
                        --  Warning case 1, missing values at start/end. Only
                        --  do the check if the number of entries is too small.

                        if (Enumeration_Pos (CHi) - Enumeration_Pos (CLo))
                              <
                           (Enumeration_Pos (AHi) - Enumeration_Pos (ALo))
                        then
                           Error_Msg_N
                             ("missing index value(s) in array aggregate??",
                              N);

                           --  Output missing value(s) at start

                           if Chars (ALo) /= Chars (CLo) then
                              Ent := Prev (CLo);

                              if Chars (ALo) = Chars (Ent) then
                                 Error_Msg_Name_1 := Chars (ALo);
                                 Error_Msg_N ("\  %??", N);
                              else
                                 Error_Msg_Name_1 := Chars (ALo);
                                 Error_Msg_Name_2 := Chars (Ent);
                                 Error_Msg_N ("\  % .. %??", N);
                              end if;
                           end if;

                           --  Output missing value(s) at end

                           if Chars (AHi) /= Chars (CHi) then
                              Ent := Next (CHi);

                              if Chars (AHi) = Chars (Ent) then
                                 Error_Msg_Name_1 := Chars (Ent);
                                 Error_Msg_N ("\  %??", N);
                              else
                                 Error_Msg_Name_1 := Chars (Ent);
                                 Error_Msg_Name_2 := Chars (AHi);
                                 Error_Msg_N ("\  % .. %??", N);
                              end if;
                           end if;

                        --  Warning case 2, dubious sliding. The First_Subtype
                        --  test distinguishes between a constrained type where
                        --  sliding is not allowed (so we will get a warning
                        --  later that Constraint_Error will be raised), and
                        --  the unconstrained case where sliding is permitted.

                        elsif (Enumeration_Pos (CHi) - Enumeration_Pos (CLo))
                                 =
                              (Enumeration_Pos (AHi) - Enumeration_Pos (ALo))
                          and then Chars (ALo) /= Chars (CLo)
                          and then
                            not Is_Constrained (First_Subtype (Etype (N)))
                        then
                           Error_Msg_N
                             ("bounds of aggregate do not match target??", N);
                        end if;
                     end;
                  end if;
               end if;

               --  If no others, aggregate bounds come from aggregate

               Aggr_Low  := Choices_Low;
               Aggr_High := Choices_High;
            end if;
         end Step_2;

      --  STEP 3: Process positional components

      else
         --  STEP 3 (A): Process positional elements

         Expr := First (Expressions (N));
         Nb_Elements := Uint_0;
         while Present (Expr) loop
            Nb_Elements := Nb_Elements + 1;

            --  Ada 2005 (AI-231)

            if Ada_Version >= Ada_2005 and then Known_Null (Expr) then
               Check_Can_Never_Be_Null (Etype (N), Expr);
            end if;

            if not Resolve_Aggr_Expr (Expr) then
               return Failure;
            end if;

            --  Check incorrect use of dynamically tagged expression

            if not Iterated then
               if Is_Tagged_Type (Etype (Expr)) then
                  Check_Dynamically_Tagged_Expression
                    (Expr => Expr,
                     Typ  => Ctyp,
                     Related_Nod => N);
               end if;
            end if;

            Next (Expr);
         end loop;

         if Present (Others_N) then
            Assoc := Last (Component_Associations (N));

            --  Ada 2005 (AI-231)

            if Ada_Version >= Ada_2005 and then Known_Null (Assoc) then
               Check_Can_Never_Be_Null (Etype (N), Expression (Assoc));
            end if;

            --  Ada 2005 (AI-287): In case of default initialized component,
            --  we delay the resolution to the expansion phase.

            if Box_Present (Assoc) then

               --  Ada 2005 (AI-287): In case of default initialization of
               --  a component, the expander will generate calls to the
               --  corresponding initialization subprogram. Check that we
               --  have a single dimension.

               if Present (Next_Index (Index)) then
                  Error_Msg_N ("nested array aggregate expected", Assoc);
                  return Failure;
               end if;

            --  ??? Checks for dynamically tagged expressions below will
            --  be only applied to iterated_component_association after
            --  expansion; in particular, errors might not be reported when
            --  -gnatc switch is used.

            elsif Nkind (Assoc) = N_Iterated_Component_Association then
               null;   --  handled above, in a loop context

            elsif not Resolve_Aggr_Expr (Expression (Assoc),
                                         Single_Elmt => False)
            then
               return Failure;

            --  Check incorrect use of dynamically tagged expression. The
            --  expression of the others choice has not been resolved yet.
            --  In order to diagnose the semantic error we create a duplicate
            --  tree to analyze it and perform the check.

            else
               declare
                  Save_Analysis : constant Boolean := Full_Analysis;
                  Expr          : constant Node_Id :=
                                    New_Copy_Tree (Expression (Assoc));

               begin
                  Expander_Mode_Save_And_Set (False);
                  Full_Analysis := False;
                  Analyze (Expr);
                  Full_Analysis := Save_Analysis;
                  Expander_Mode_Restore;

                  if Is_Tagged_Type (Etype (Expr)) then
                     Check_Dynamically_Tagged_Expression
                       (Expr        => Expr,
                        Typ         => Ctyp,
                        Related_Nod => N);
                  end if;
               end;
            end if;
         end if;

         --  STEP 3 (B): Compute the aggregate bounds

         if Present (Others_N) then
            Get_Index_Bounds (Index_Constr, Aggr_Low, Aggr_High);

         else
            if Others_Allowed then
               Get_Index_Bounds (Index_Constr, Aggr_Low, Discard);
            else
               Aggr_Low := Index_Typ_Low;
            end if;

            --  Report a warning when the index type of a null array aggregate
            --  is a modular type or an enumeration type, and we know that
            --  we will not be able to compute its high bound at runtime
            --  (AI22-0100-2).

            if Nb_Elements = Uint_0
              and then Cannot_Compute_High_Bound (Index_Constr)
            then
               --  Use the low bound value for the high-bound value to avoid
               --  reporting spurious errors; this value will not be used at
               --  runtime because this aggregate will be replaced by a raise
               --  CE node.

               Aggr_High := Aggr_Low;

               Report_Null_Array_Constraint_Error (N, Index_Typ);
               Set_Raises_Constraint_Error (N);

            elsif Nb_Elements = Uint_0 then
               Aggr_High := Subtract (Uint_1, To => Aggr_Low);
               Check_Bound (Index_Base_High, Aggr_High);

            else
               Aggr_High := Add (Nb_Elements - 1, To => Aggr_Low);
               Check_Bound (Index_Base_High, Aggr_High);
            end if;
         end if;
      end if;

      --  STEP 4: Perform static aggregate checks and save the bounds

      --  Check (A)

      Check_Bounds (Index_Typ_Low, Index_Typ_High, Aggr_Low, Aggr_High);
      Check_Bounds (Index_Base_Low, Index_Base_High, Aggr_Low, Aggr_High);

      --  Check (B)

      if Present (Others_N) and then Nb_Discrete_Choices > 0 then
         Check_Bounds (Aggr_Low, Aggr_High, Choices_Low, Choices_High);
         Check_Bounds (Index_Typ_Low, Index_Typ_High,
                       Choices_Low, Choices_High);
         Check_Bounds (Index_Base_Low, Index_Base_High,
                       Choices_Low, Choices_High);

      --  Check (C)

      elsif Present (Others_N) and then Nb_Elements > 0 then
         Check_Length (Aggr_Low, Aggr_High, Nb_Elements);
         Check_Length (Index_Typ_Low, Index_Typ_High, Nb_Elements);
         Check_Length (Index_Base_Low, Index_Base_High, Nb_Elements);
      end if;

      if Raises_Constraint_Error (Aggr_Low)
        or else Raises_Constraint_Error (Aggr_High)
      then
         Set_Raises_Constraint_Error (N);
      end if;

      Aggr_Low := Duplicate_Subexpr (Aggr_Low);

      --  Do not duplicate Aggr_High if Aggr_High = Aggr_Low + Nb_Elements
      --  since the addition node returned by Add is not yet analyzed. Attach
      --  to tree and analyze first. Reset analyzed flag to ensure it will get
      --  analyzed when it is a literal bound whose type must be properly set.

      if Present (Others_N) or else Nb_Discrete_Choices > 0 then
         Aggr_High := Duplicate_Subexpr (Aggr_High);

         if Etype (Aggr_High) = Universal_Integer then
            Set_Analyzed (Aggr_High, False);
         end if;
      end if;

      --  If the aggregate already has bounds attached to it, it means this is
      --  a positional aggregate created as an optimization by
      --  Exp_Aggr.Convert_To_Positional, so we don't want to change those
      --  bounds, unless they depend on discriminants. If they do, we have to
      --  perform analysis in the current context.

      if Present (Aggregate_Bounds (N))
        and then No (Others_N)
        and then not Depends_On_Discriminant (Aggregate_Bounds (N))
        and then not Comes_From_Source (N)
      then
         Aggr_Low  := Low_Bound  (Aggregate_Bounds (N));
         Aggr_High := High_Bound (Aggregate_Bounds (N));
      end if;

      Set_Aggregate_Bounds
        (N, Make_Range (Loc, Low_Bound => Aggr_Low, High_Bound => Aggr_High));

      --  The bounds may contain expressions that must be inserted upwards.
      --  Attach them fully to the tree. After analysis, remove side effects
      --  from upper bound, if still needed.

      Set_Parent (Aggregate_Bounds (N), N);
      Analyze_And_Resolve (Aggregate_Bounds (N), Index_Typ);
      Check_Unset_Reference (Aggregate_Bounds (N));

      if No (Others_N) and then Nb_Discrete_Choices = 0 then
         Set_High_Bound
           (Aggregate_Bounds (N),
            Duplicate_Subexpr (High_Bound (Aggregate_Bounds (N))));
      end if;

      --  Check the dimensions of each component in the array aggregate

      Analyze_Dimension_Array_Aggregate (N, Ctyp);

      if Serious_Errors_Detected /= Saved_SED then
         return Failure;
      end if;

      return Success;
   end Resolve_Array_Aggregate;

   ---------------------------------
   -- Resolve_Container_Aggregate --
   ---------------------------------

   procedure Resolve_Container_Aggregate (N : Node_Id; Typ : Entity_Id) is
      procedure Resolve_Iterated_Association
        (Comp      : Node_Id;
         Key_Type  : Entity_Id;
         Elmt_Type : Entity_Id);
      --  Resolve choices and expression in an iterated component association
      --  or an iterated element association, which has a key_expression.
      --  This is similar but not identical to the handling of this construct
      --  in an array aggregate.
      --  For a named container, the type of each choice must be compatible
      --  with the key type. For a positional container, the choice must be
      --  a subtype indication or an iterator specification that determines
      --  an element type.

      Asp   : constant Node_Id := Find_Value_Of_Aspect (Typ, Aspect_Aggregate);

      Empty_Subp          : Node_Id := Empty;
      Add_Named_Subp      : Node_Id := Empty;
      Add_Unnamed_Subp    : Node_Id := Empty;
      New_Indexed_Subp    : Node_Id := Empty;
      Assign_Indexed_Subp : Node_Id := Empty;

      ----------------------------------
      -- Resolve_Iterated_Association --
      ----------------------------------

      procedure Resolve_Iterated_Association
        (Comp      : Node_Id;
         Key_Type  : Entity_Id;
         Elmt_Type : Entity_Id)
      is
         Loc           : constant Source_Ptr := Sloc (N);
         Choice        : Node_Id;
         Copy          : Node_Id;
         Ent           : Entity_Id;
         Expr          : Node_Id;
         Key_Expr      : Node_Id := Empty;
         Id            : Entity_Id;
         Id_Name       : Name_Id;
         Typ           : Entity_Id := Empty;
         Loop_Param_Id : Entity_Id := Empty;

      begin
         Error_Msg_Ada_2022_Feature ("iterated component", Loc);

         --  If this is an Iterated_Element_Association then either a
         --  an Iterator_Specification or a Loop_Parameter specification
         --  is present.

         if Nkind (Comp) = N_Iterated_Element_Association then

            --  Create a temporary scope to avoid some modifications from
            --  escaping the Analyze call below. The original Tree will be
            --  reanalyzed later.

            Ent := New_Internal_Entity
                     (E_Loop, Current_Scope, Sloc (Comp), 'L');
            Set_Etype  (Ent, Standard_Void_Type);
            Set_Parent (Ent, Parent (Comp));
            Push_Scope (Ent);

            if Present (Loop_Parameter_Specification (Comp)) then
               Copy := Copy_Separate_Tree (Comp);
               Set_Parent (Copy, Parent (Comp));

               Analyze
                 (Loop_Parameter_Specification (Copy));

               if Present (Iterator_Specification (Copy)) then
                  Loop_Param_Id :=
                    Defining_Identifier (Iterator_Specification (Copy));
               else
                  Loop_Param_Id :=
                    Defining_Identifier (Loop_Parameter_Specification (Copy));
               end if;

               Id_Name := Chars (Loop_Param_Id);
            else
               Copy := Copy_Separate_Tree (Iterator_Specification (Comp));
               Analyze (Copy);

               Loop_Param_Id := Defining_Identifier (Copy);

               Id_Name := Chars (Loop_Param_Id);
            end if;

            --  Key expression must have the type of the key. We preanalyze
            --  a copy of the original expression, because it will be
            --  reanalyzed and copied as needed during expansion of the
            --  corresponding loop.

            Key_Expr := Key_Expression (Comp);
            if Present (Key_Expr) then
               if No (Add_Named_Subp) then
                  Error_Msg_N
                    ("iterated_element_association with key_expression only "
                       & "allowed for container type with Add_Named operation "
                       & "(RM22 4.3.5(24))",
                     Comp);
               else
                  Preanalyze_And_Resolve (New_Copy_Tree (Key_Expr), Key_Type);
               end if;
            end if;
            End_Scope;

            Typ := Etype (Loop_Param_Id);

         elsif Present (Iterator_Specification (Comp)) then
            --  Create a temporary scope to avoid some modifications from
            --  escaping the Analyze call below. The original Tree will be
            --  reanalyzed later.

            Ent := New_Internal_Entity
                     (E_Loop, Current_Scope, Sloc (Comp), 'L');
            Set_Etype  (Ent, Standard_Void_Type);
            Set_Parent (Ent, Parent (Comp));
            Push_Scope (Ent);

            Copy := Copy_Separate_Tree (Iterator_Specification (Comp));

            Loop_Param_Id :=
              Defining_Identifier (Iterator_Specification (Comp));

            Id_Name := Chars (Loop_Param_Id);

            Preanalyze (Copy);

            End_Scope;

            Typ := Etype (Defining_Identifier (Copy));

         else
            Choice := First (Discrete_Choices (Comp));

            --  A copy of Choice is made before it's analyzed, to preserve
            --  prefixed calls in their original form, because otherwise the
            --  analysis of Choice can transform such calls to normal form,
            --  and the later analysis of an iterator_specification created
            --  below in the case of a function-call choice may trigger an
            --  error on the call (in the case where the function is not
            --  directly visible).

            Copy := Copy_Separate_Tree (Choice);

            --  This is an N_Component_Association with a Defining_Identifier
            --  and Discrete_Choice_List, but the latter can only have a single
            --  choice, as it's a stand-in for a Loop_Parameter_Specification
            --  (or possibly even an Iterator_Specification, see below).

            pragma Assert (No (Next (Choice)));

            Analyze (Choice);

            --  Choice can be a subtype name, a range, or an expression

            if Is_Entity_Name (Choice)
              and then Is_Type (Entity (Choice))
              and then Present (Key_Type)
              and then Base_Type (Entity (Choice)) = Base_Type (Key_Type)
            then
               null;

            elsif Is_Object_Reference (Choice) then
               declare
                  I_Spec : constant Node_Id :=
                    Make_Iterator_Specification (Sloc (N),
                      Defining_Identifier =>
                        Relocate_Node (Defining_Identifier (Comp)),
                      Name                => Copy,
                      Reverse_Present     => Reverse_Present (Comp),
                      Iterator_Filter     => Empty,
                      Subtype_Indication  => Empty);
               begin
                  Set_Iterator_Specification (Comp, I_Spec);
                  Set_Defining_Identifier (Comp, Empty);

                  Resolve_Iterated_Association (Comp, Key_Type, Elmt_Type);
                  --  Recursive call to expand association as iterator_spec

                  return;
               end;

            elsif Present (Key_Type) then
               Analyze_And_Resolve (Choice, Key_Type);
               Typ := Key_Type;

            else
               Typ := Etype (Choice);  --  assume unique for now
            end if;

            Loop_Param_Id :=
              Defining_Identifier (Comp);

            Id_Name := Chars (Loop_Param_Id);
         end if;

         --  Create a scope in which to introduce an index, which is usually
         --  visible in the expression for the component, and needed for its
         --  analysis.

         Id := Make_Defining_Identifier (Sloc (Comp), Id_Name);
         Ent := New_Internal_Entity (E_Loop,
                  Current_Scope, Sloc (Comp), 'L');
         Set_Etype  (Ent, Standard_Void_Type);
         Set_Parent (Ent, Parent (Comp));
         Push_Scope (Ent);

         --  Insert and decorate the loop variable in the current scope.
         --  The expression has to be analyzed once the loop variable is
         --  directly visible. Mark the variable as referenced to prevent
         --  spurious warnings, given that subsequent uses of its name in the
         --  expression will reference the internal (synonym) loop variable.

         Enter_Name (Id);

         pragma Assert (Present (Typ));
         Set_Etype (Id, Typ);

         Mutate_Ekind (Id, E_Variable);
         Set_Is_Not_Self_Hidden (Id);
         Set_Scope (Id, Ent);
         Set_Referenced (Id);

         --  Check for violation of 4.3.5(27/5)

         if No (Key_Expr)
           and then Present (Key_Type)
           and then
             (Is_Indexed_Aggregate (N, Add_Unnamed_Subp, New_Indexed_Subp)
               or else Present (Add_Named_Subp))
           and then Base_Type (Key_Type) /= Base_Type (Typ)
         then
            Error_Msg_Node_2 := Key_Type;
            Error_Msg_NE
              ("loop parameter type & must be same as key type & " &
               "(RM22 4.3.5(27))", Loop_Param_Id, Typ);
         end if;

         --  Analyze a copy of the expression, to verify legality. We use
         --  a copy because the expression will be analyzed anew when the
         --  enclosing aggregate is expanded, and the construct is rewritten
         --  as a loop with a new index variable.

         Expr := Copy_Separate_Tree (Expression (Comp));
         Set_Parent (Expr, Comp);
         Preanalyze_And_Resolve (Expr, Elmt_Type);
         End_Scope;
      end Resolve_Iterated_Association;

   --  Start of processing for Resolve_Container_Aggregate

   begin
      pragma Assert (Nkind (Asp) = N_Aggregate);

      Set_Etype (N, Typ);
      Parse_Aspect_Aggregate (Asp,
        Empty_Subp, Add_Named_Subp, Add_Unnamed_Subp,
        New_Indexed_Subp, Assign_Indexed_Subp);

      if Present (First (Expressions (N)))
        and then Present (First (Component_Associations (N)))
      then
         Error_Msg_N
           (Msg        =>
              "container aggregate cannot be both positional and named",
            N          => N,
            Error_Code => GNAT0006,
            Spans      =>
              (1 =>
                 Secondary_Labeled_Span
                   (First (Expressions (N)), "positional element "),
               2 =>
                 Secondary_Labeled_Span
                   (First (Component_Associations (N)), "named element")));
         return;
      end if;

      if Present (Add_Unnamed_Subp)
        and then No (New_Indexed_Subp)
        and then Present (Entity (Add_Unnamed_Subp))
        and then Entity (Add_Unnamed_Subp) /= Any_Id
      then
         declare
            Elmt_Type : constant Entity_Id :=
              Etype (Next_Formal
                (First_Formal (Entity (Add_Unnamed_Subp))));
            Comp : Node_Id;

         begin
            if Present (Expressions (N)) then
               --  positional aggregate

               Comp := First (Expressions (N));
               while Present (Comp) loop
                  Analyze_And_Resolve (Comp, Elmt_Type);
                  Next (Comp);
               end loop;
            end if;

            --  Empty aggregate, to be replaced by Empty during
            --  expansion, or iterated component association.

            if Present (Component_Associations (N)) then
               declare
                  Comp : Node_Id := First (Component_Associations (N));
               begin
                  while Present (Comp) loop
                     if Nkind (Comp) in
                       N_Iterated_Component_Association |
                       N_Iterated_Element_Association
                     then
                        Resolve_Iterated_Association
                          (Comp, Empty, Elmt_Type);
                     else
                        Error_Msg_N ("illegal component association "
                          & "for unnamed container aggregate", Comp);
                        return;
                     end if;

                     Next (Comp);
                  end loop;
               end;
            end if;
         end;

      elsif Present (Add_Named_Subp)
        and then Present (Entity (Add_Named_Subp))
        and then Entity (Add_Named_Subp) /= Any_Id
      then
         declare
            --  Retrieves types of container, key, and element from the
            --  specified insertion procedure.

            Container : constant Entity_Id :=
              First_Formal (Entity (Add_Named_Subp));
            Key_Type  : constant Entity_Id := Etype (Next_Formal (Container));
            Elmt_Type : constant Entity_Id :=
                                 Etype (Next_Formal (Next_Formal (Container)));

            Comp_Assocs : constant List_Id := Component_Associations (N);
            Comp        : Node_Id;
            Choice      : Node_Id;

         begin
            --  In the Add_Named case, the aggregate must consist of named
            --  associations (Add_Unnnamed is not allowed), so we issue an
            --  error if there are positional associations.

            if No (Comp_Assocs)
              and then Present (Expressions (N))
            then
               Error_Msg_N ("container aggregate must be "
                 & "named, not positional", N);
               return;
            end if;

            Comp := First (Comp_Assocs);
            while Present (Comp) loop
               if Nkind (Comp) = N_Component_Association then
                  Choice := First (Choices (Comp));

                  while Present (Choice) loop
                     Analyze_And_Resolve (Choice, Key_Type);
                     Next (Choice);
                  end loop;

                  Analyze_And_Resolve (Expression (Comp), Elmt_Type);

               elsif Nkind (Comp) in
                 N_Iterated_Component_Association |
                 N_Iterated_Element_Association
               then
                  Resolve_Iterated_Association
                    (Comp, Key_Type, Elmt_Type);
               end if;

               Next (Comp);
            end loop;
         end;

      elsif Present (Assign_Indexed_Subp)
        and then Present (Entity (Assign_Indexed_Subp))
        and then Entity (Assign_Indexed_Subp) /= Any_Id
      then
         --  Indexed Aggregate. Positional or indexed component
         --  can be present, but not both. Choices must be static
         --  values or ranges with static bounds.

         declare
            Container : constant Entity_Id :=
              First_Formal (Entity (Assign_Indexed_Subp));
            Index_Type : constant Entity_Id := Etype (Next_Formal (Container));
            Comp_Type  : constant Entity_Id :=
                                 Etype (Next_Formal (Next_Formal (Container)));
            Comp        : Node_Id;
            Choice      : Node_Id;
            Num_Choices : Nat := 0;

            Hi_Val : Uint;
            Lo_Val : Uint;
         begin
            if Present (Expressions (N)) then
               Comp := First (Expressions (N));
               while Present (Comp) loop
                  Analyze_And_Resolve (Comp, Comp_Type);
                  Next (Comp);
               end loop;
            end if;

            if Present (Component_Associations (N))
              and then not Is_Empty_List (Component_Associations (N))
            then
               Comp := First (Component_Associations (N));

               while Present (Comp) loop
                  if Nkind (Comp) = N_Component_Association then
                     Choice := First (Choices (Comp));

                     while Present (Choice) loop
                        Analyze_And_Resolve (Choice, Index_Type);
                        Num_Choices := Num_Choices + 1;
                        Next (Choice);
                     end loop;

                     if not Box_Present (Comp) then
                        Analyze_And_Resolve (Expression (Comp), Comp_Type);
                     end if;

                  elsif Nkind (Comp) in
                    N_Iterated_Component_Association |
                    N_Iterated_Element_Association
                  then
                     Resolve_Iterated_Association
                       (Comp, Index_Type, Comp_Type);

                     --  Check the legality rule of RM22 4.3.5(28/5). Note that
                     --  Is_Indexed_Aggregate can change its status (to False)
                     --  as a result of calling Resolve_Iterated_Association,
                     --  due to possible expansion of iterator_specifications
                     --  there.

                     if Is_Indexed_Aggregate
                          (N, Add_Unnamed_Subp, New_Indexed_Subp)
                     then
                        if Nkind (Comp) = N_Iterated_Element_Association then
                           if Present (Loop_Parameter_Specification (Comp))
                           then
                              if Present (Iterator_Filter
                                   (Loop_Parameter_Specification (Comp)))
                              then
                                 Error_Msg_N
                                   ("iterator filter not allowed " &
                                    "in indexed aggregate (RM22 4.3.5(28))",
                                    Iterator_Filter
                                      (Loop_Parameter_Specification (Comp)));
                                 return;

                              elsif Present (Key_Expression (Comp)) then
                                 Error_Msg_N
                                   ("key expression not allowed " &
                                    "in indexed aggregate (RM22 4.3.5(28))",
                                    Key_Expression (Comp));
                                 return;
                              end if;

                           elsif Present (Iterator_Specification (Comp)) then
                              Error_Msg_N
                                ("iterator specification not allowed " &
                                 "in indexed aggregate (RM22 4.3.5(28))",
                                 Iterator_Specification (Comp));
                              return;
                           end if;

                        elsif Nkind (Comp) = N_Iterated_Component_Association
                          and then Present (Iterator_Specification (Comp))
                        then
                           Error_Msg_N
                             ("iterator specification not allowed " &
                              "in indexed aggregate (RM22 4.3.5(28))",
                              Iterator_Specification (Comp));
                           return;
                        end if;
                     end if;

                     Num_Choices := Num_Choices + 1;
                  end if;

                  Next (Comp);
               end loop;

               --  The component associations in an indexed aggregate
               --  must denote a contiguous set of static values. We
               --  build a table of values/ranges and sort it, as is done
               --  elsewhere for case statements and array aggregates.
               --  If the aggregate has a single iterated association it
               --  is allowed to be nonstatic and there is nothing to check.

               if Num_Choices > 1 then
                  declare
                     Table     : Case_Table_Type (1 .. Num_Choices);
                     No_Choice : Pos := 1;
                     Lo, Hi    : Node_Id;

                  --  Traverse aggregate to determine size of needed table.
                  --  Verify that bounds are static and that loops have no
                  --  filters or key expressions.

                  begin
                     Comp := First (Component_Associations (N));
                     while Present (Comp) loop

                        --  If Nkind is N_Iterated_Component_Association,
                        --  this corresponds to an iterator_specification
                        --  with a loop_parameter_specification, and we
                        --  have to pick up Discrete_Choices. In this case
                        --  there will be just one "choice", which will
                        --  typically be a range.

                        if Nkind (Comp) = N_Iterated_Component_Association
                        then
                           Choice := First (Discrete_Choices (Comp));

                        --  Case where there's a list of choices

                        else
                           Choice := First (Choices (Comp));
                        end if;

                        while Present (Choice) loop
                           Get_Index_Bounds (Choice, Lo, Hi);
                           Table (No_Choice).Choice := Choice;
                           Table (No_Choice).Lo := Lo;
                           Table (No_Choice).Hi := Hi;

                           --  Verify staticness of value or range

                           if not Is_Static_Expression (Lo)
                             or else not Is_Static_Expression (Hi)
                           then
                              Error_Msg_N
                                ("nonstatic expression for index " &
                                  "for indexed aggregate", Choice);
                              return;
                           end if;

                           No_Choice := No_Choice + 1;
                           Next (Choice);
                        end loop;

                        Next (Comp);
                     end loop;

                     Sort_Case_Table (Table);

                     for J in 1 .. Num_Choices - 1 loop
                        Hi_Val := Expr_Value (Table (J).Hi);
                        Lo_Val := Expr_Value (Table (J + 1).Lo);

                        if Lo_Val = Hi_Val then
                           Error_Msg_N
                             ("duplicate index in indexed aggregate",
                               Table (J + 1).Choice);
                           exit;

                        elsif Lo_Val < Hi_Val then
                           Error_Msg_N
                             ("overlapping indices in indexed aggregate",
                               Table (J + 1).Choice);
                           exit;

                        elsif Lo_Val > Hi_Val + 1 then
                           Error_Msg_N
                             ("missing index values", Table (J + 1).Choice);
                           exit;
                        end if;
                     end loop;
                  end;
               end if;
            end if;
         end;
      end if;
   end Resolve_Container_Aggregate;

   -----------------------------
   -- Resolve_Delta_Aggregate --
   -----------------------------

   procedure Resolve_Delta_Aggregate (N : Node_Id; Typ : Entity_Id) is
      Base : constant Node_Id := Expression (N);

   begin
      Error_Msg_Ada_2022_Feature ("delta aggregate", Sloc (N));

      if not Is_Composite_Type (Typ) then
         Error_Msg_N ("not a composite type", N);
      end if;

      Analyze_And_Resolve (Base, Typ);

      if Is_Array_Type (Typ) then
         --  For an array_delta_aggregate, the base_expression and each
         --  expression in every array_component_association shall be of a
         --  nonlimited type; RM 4.3.4(13/5). However, to prevent repeated
         --  errors we only check the base expression and not array component
         --  associations.

         if Is_Limited_Type (Etype (Base)) then
            Error_Msg_N
              ("array delta aggregate shall be of a nonlimited type", Base);
            Explain_Limited_Type (Etype (Base), Base);
         end if;

         Resolve_Delta_Array_Aggregate (N, Typ);
      else

         --  Delta aggregates for record types must use parentheses,
         --  not square brackets.

         if Is_Homogeneous_Aggregate (N) then
            Error_Msg_N
              ("delta aggregates for record types must use (), not '[']", N);
         end if;

         --  The base_expression of a record_delta_aggregate can be of a
         --  limited type only if it is newly constructed; RM 7.5(2.1/5).

         Check_Expr_OK_In_Limited_Aggregate (Base);

         Resolve_Delta_Record_Aggregate (N, Typ);
      end if;

      declare
         Assoc  : Node_Id;
         Choice : Node_Id;

         procedure Check_For_Bad_Dd_Component_Choice (Choice : Node_Id);
         --  Enforce the GNAT RM rule that a deep delta aggregate choice
         --  cannot name a discriminant-dependent component if the
         --  immediately enclosing object's subtype is unconstrained and the
         --  prefix of the component includes at least one array indexing.
         --  [Note: The motivation for this rule is unclear. The GNAT RM
         --  gives a rationale for this particular rule, but it still
         --  seems dubious.]

         ---------------------------------------
         -- Check_For_Bad_Dd_Component_Choice --
         ---------------------------------------

         procedure Check_For_Bad_Dd_Component_Choice (Choice : Node_Id) is
            Pref         : Node_Id := Choice;
            Dd_Comp_Name : Node_Id := Empty;
         begin
            loop
               case Nkind (Pref) is
                  when N_Selected_Component =>
                     declare
                        Comp : constant Entity_Id
                          := Entity (Selector_Name (Pref));

                        Enclosing_Type : Entity_Id := Etype (Prefix (Pref));
                     begin
                        if Is_Declared_Within_Variant (Comp)
                          or else Has_Discriminant_Dependent_Constraint (Comp)
                        then
                           if not Has_Discriminants (Enclosing_Type) then
                              --  a deep delta array aggregate choice like
                              --     (Index_Value).Record_Component => ...
                              Enclosing_Type := Component_Type (Etype (N));
                           end if;

                           if not Is_Constrained (Enclosing_Type) then
                              Dd_Comp_Name := Selector_Name (Pref);
                           end if;
                        end if;
                     end;

                  when N_Indexed_Component =>
                     exit when Present (Dd_Comp_Name);

                  when N_Identifier =>
                     return;

                  when others =>
                     exit;
               end case;
               Pref := Prefix (Pref);
            end loop;

            if Present (Dd_Comp_Name) then
               --  It would be difficult to explain the whole rule briefly,
               --  so we just say "illegal".

               Error_Msg_N
                 ("illegal discriminant-dependent component &" &
                  " in deep delta aggregate choice", Dd_Comp_Name);
            end if;
         end Check_For_Bad_Dd_Component_Choice;

      begin
         Assoc := First (Component_Associations (N));
         while Present (Assoc) loop
            Choice := First (Choice_List (Assoc));
            while Present (Choice) loop
               Check_For_Bad_Dd_Component_Choice (Choice);
               Next (Choice);
            end loop;
            Next (Assoc);
         end loop;
      end;

      Set_Etype (N, Typ);
   end Resolve_Delta_Aggregate;

   -----------------------------------
   -- Resolve_Delta_Array_Aggregate --
   -----------------------------------

   procedure Resolve_Delta_Array_Aggregate (N : Node_Id; Typ : Entity_Id) is
      Deltas     : constant List_Id   := Component_Associations (N);
      Index_Type : constant Entity_Id := Etype (First_Index (Typ));

      Assoc  : Node_Id;
      Choice : Node_Id;
      Expr   : Node_Id;

      Deep_Choice_Seen : Boolean := False;

   begin
      Assoc := First (Deltas);
      while Present (Assoc) loop
         if Nkind (Assoc) = N_Iterated_Component_Association then
            Choice := First (Choice_List (Assoc));
            while Present (Choice) loop
               if Nkind (Choice) = N_Others_Choice then
                  Error_Msg_N
                    ("OTHERS not allowed in delta aggregate", Choice);

               elsif Nkind (Choice) = N_Subtype_Indication then
                  Resolve_Discrete_Subtype_Indication
                    (Choice, Base_Type (Index_Type));

               else
                  Analyze_And_Resolve (Choice, Index_Type);
               end if;

               Next (Choice);
            end loop;

            declare
               Id  : constant Entity_Id := Defining_Identifier (Assoc);
               Ent : constant Entity_Id :=
                       New_Internal_Entity
                         (E_Loop, Current_Scope, Sloc (Assoc), 'L');

            begin
               Set_Etype  (Ent, Standard_Void_Type);
               Set_Parent (Ent, Assoc);
               Push_Scope (Ent);

               if No (Scope (Id)) then
                  Set_Etype (Id, Index_Type);
                  Mutate_Ekind (Id, E_Variable);
                  Set_Is_Not_Self_Hidden (Id);
                  Set_Scope (Id, Ent);
               end if;

               Enter_Name (Id);

               --  Analyze a copy of the expression, to verify legality. We use
               --  a copy because the expression will be analyzed anew when the
               --  enclosing aggregate is expanded, and the construct is
               --  rewritten as a loop with a new index variable.

               Expr := Copy_Separate_Tree (Expression (Assoc));
               Set_Parent (Expr, Assoc);
               Preanalyze_And_Resolve (Expr, Component_Type (Typ));
               End_Scope;
            end;

         else
            Choice := First (Choice_List (Assoc));
            while Present (Choice) loop
               if Is_Deep_Choice (Choice, Typ) then
                  pragma Assert (All_Extensions_Allowed);
                  Deep_Choice_Seen := True;

                  --  a deep delta aggregate
                  Resolve_Deep_Delta_Assoc (Assoc, Typ);
               else
                  Analyze (Choice);

                  if Nkind (Choice) = N_Others_Choice then
                     Error_Msg_N
                       ("OTHERS not allowed in delta aggregate", Choice);

                  elsif Is_Entity_Name (Choice)
                    and then Is_Type (Entity (Choice))
                  then
                     --  Choice covers a range of values

                     if Base_Type (Entity (Choice)) /=
                        Base_Type (Index_Type)
                     then
                        Error_Msg_NE
                          ("choice does not match index type of &",
                           Choice, Typ);
                     end if;

                  elsif Nkind (Choice) = N_Subtype_Indication then
                     Resolve_Discrete_Subtype_Indication
                       (Choice, Base_Type (Index_Type));

                  else
                     Resolve (Choice, Index_Type);
                  end if;
               end if;

               Next (Choice);
            end loop;

            --  For an array_delta_aggregate, the array_component_association
            --  shall not use the box symbol <>; RM 4.3.4(11/5).

            pragma Assert
              (Box_Present (Assoc) xor Present (Expression (Assoc)));

            if Box_Present (Assoc) then
               Error_Msg_N
                 ("'<'> in array delta aggregate is not allowed", Assoc);
            elsif not Deep_Choice_Seen then
               Analyze_And_Resolve (Expression (Assoc), Component_Type (Typ));
            end if;
         end if;

         Next (Assoc);
      end loop;
   end Resolve_Delta_Array_Aggregate;

   ------------------------------------
   -- Resolve_Delta_Record_Aggregate --
   ------------------------------------

   procedure Resolve_Delta_Record_Aggregate (N : Node_Id; Typ : Entity_Id) is

      --  Variables used to verify that discriminant-dependent components
      --  appear in the same variant.

      Comp_Ref : Entity_Id := Empty; -- init to avoid warning
      Variant  : Node_Id;

      procedure Check_Variant (Id : Node_Id);
      --  If a given component of the delta aggregate appears in a variant
      --  part, verify that it is within the same variant as that of previous
      --  specified variant components of the delta.

      function Get_Component_Type
        (Selector : Node_Id; Enclosing_Type : Entity_Id) return Entity_Id;
      --  Locate component with a given name and return its type.
      --  If none found then report error and return Empty.

      function Nested_In (V1 : Node_Id; V2 : Node_Id) return Boolean;
      --  Determine whether variant V1 is within variant V2

      function Variant_Depth (N : Node_Id) return Natural;
      --  Determine the distance of a variant to the enclosing type declaration

      --------------------
      --  Check_Variant --
      --------------------

      procedure Check_Variant (Id : Node_Id) is
         Comp         : Entity_Id;
         Comp_Variant : Node_Id;

      begin
         if not Has_Discriminants (Typ) then
            return;
         end if;

         Comp := First_Entity (Typ);
         while Present (Comp) loop
            exit when Chars (Comp) = Chars (Id);
            Next_Component (Comp);
         end loop;

         --  Find the variant, if any, whose component list includes the
         --  component declaration.

         Comp_Variant := Parent (Parent (List_Containing (Parent (Comp))));
         if Nkind (Comp_Variant) = N_Variant then
            if No (Variant) then
               Variant  := Comp_Variant;
               Comp_Ref := Comp;

            elsif Variant /= Comp_Variant then
               declare
                  D1 : constant Integer := Variant_Depth (Variant);
                  D2 : constant Integer := Variant_Depth (Comp_Variant);

               begin
                  if D1 = D2
                    or else
                      (D1 > D2 and then not Nested_In (Variant, Comp_Variant))
                    or else
                      (D2 > D1 and then not Nested_In (Comp_Variant, Variant))
                  then
                     pragma Assert (Present (Comp_Ref));
                     Error_Msg_Node_2 := Comp_Ref;
                     Error_Msg_NE
                       ("& and & appear in different variants", Id, Comp);

                  --  Otherwise retain the deeper variant for subsequent tests

                  elsif D2 > D1 then
                     Variant := Comp_Variant;
                  end if;
               end;
            end if;
         end if;
      end Check_Variant;

      ------------------------
      -- Get_Component_Type --
      ------------------------

      function Get_Component_Type
        (Selector : Node_Id; Enclosing_Type : Entity_Id) return Entity_Id
      is
         Comp : Entity_Id;
      begin
         case Nkind (Selector) is
            when N_Selected_Component | N_Indexed_Component =>
               --  a deep delta aggregate choice

               declare
                  Prefix_Type : constant Entity_Id :=
                    Get_Component_Type (Prefix (Selector), Enclosing_Type);
               begin
                  if No (Prefix_Type) then
                     pragma Assert (Serious_Errors_Detected > 0);
                     return Empty;
                  end if;

                  --  Set the type of the prefix for GNATprove

                  Set_Etype (Prefix (Selector), Prefix_Type);

                  if Nkind (Selector) = N_Selected_Component then
                     return Get_Component_Type
                              (Selector_Name (Selector),
                               Enclosing_Type => Prefix_Type);
                  elsif not Is_Array_Type (Prefix_Type) then
                     Error_Msg_NE
                       ("type& is not an array type",
                        Selector, Prefix_Type);
                  elsif Number_Dimensions (Prefix_Type) /= 1 then
                     Error_Msg_NE
                       ("array type& not one-dimensional",
                        Selector, Prefix_Type);
                  elsif List_Length (Expressions (Selector)) /= 1 then
                     Error_Msg_NE
                       ("wrong number of indices for array type&",
                        Selector, Prefix_Type);
                  else
                     Analyze_And_Resolve
                       (First (Expressions (Selector)),
                        Etype (First_Index (Prefix_Type)));
                     return Component_Type (Prefix_Type);
                  end if;
               end;

            when others =>
               null;
         end case;

         Comp := First_Entity (Enclosing_Type);
         while Present (Comp) loop
            if Chars (Comp) = Chars (Selector) then
               if Ekind (Comp) = E_Discriminant then
                  Error_Msg_N ("delta cannot apply to discriminant", Selector);
               end if;

               Set_Entity (Selector, Comp);
               Set_Etype  (Selector, Etype (Comp));

               return Etype (Comp);
            end if;

            Next_Entity (Comp);
         end loop;

         Error_Msg_NE
           ("type& has no component with this name", Selector, Enclosing_Type);
         return Empty;
      end Get_Component_Type;

      ---------------
      -- Nested_In --
      ---------------

      function Nested_In (V1, V2 : Node_Id) return Boolean is
         Par : Node_Id;

      begin
         Par := Parent (V1);
         while Nkind (Par) /= N_Full_Type_Declaration loop
            if Par = V2 then
               return True;
            end if;

            Par := Parent (Par);
         end loop;

         return False;
      end Nested_In;

      -------------------
      -- Variant_Depth --
      -------------------

      function Variant_Depth (N : Node_Id) return Natural is
         Depth : Natural;
         Par   : Node_Id;

      begin
         Depth := 0;
         Par   := Parent (N);
         while Nkind (Par) /= N_Full_Type_Declaration loop
            Depth := Depth + 1;
            Par   := Parent (Par);
         end loop;

         return Depth;
      end Variant_Depth;

      --  Local variables

      Deltas : constant List_Id := Component_Associations (N);

      Assoc        : Node_Id;
      Choice       : Node_Id;
      Comp_Type    : Entity_Id := Empty; -- init to avoid warning
      Deep_Choice  : Boolean;
      Choice_Count : Natural := 0;

   --  Start of processing for Resolve_Delta_Record_Aggregate

   begin
      Variant := Empty;

      Assoc := First (Deltas);
      while Present (Assoc) loop
         Choice := First (Choice_List (Assoc));
         while Present (Choice) loop
            Choice_Count := Choice_Count + 1;

            Deep_Choice := Nkind (Choice) /= N_Identifier;
            if Deep_Choice then
               Error_Msg_GNAT_Extension
                 ("deep delta aggregate", Sloc (Choice));
            end if;

            Comp_Type := Get_Component_Type
                          (Selector => Choice, Enclosing_Type => Typ);

            --  Set the type of the choice for GNATprove

            if Deep_Choice then
               Set_Etype (Choice, Comp_Type);
            end if;

            if Present (Comp_Type) then
               if not Deep_Choice then
                  --  ??? Not clear yet how RM 4.3.1(17.7) applies to a
                  --  deep delta aggregate.
                  Check_Variant (Choice);
               end if;
            else
               Comp_Type := Any_Type;
            end if;

            Next (Choice);
         end loop;

         pragma Assert (Present (Comp_Type));

         --  A record_component_association in record_delta_aggregate shall not
         --  use the box compound delimiter <> rather than an expression; see
         --  RM 4.3.1(17.3/5).

         pragma Assert (Present (Expression (Assoc)) xor Box_Present (Assoc));

         if Box_Present (Assoc) then
            Error_Msg_N
              ("'<'> in record delta aggregate is not allowed", Assoc);
         else
            Analyze_And_Resolve (Expression (Assoc), Comp_Type);

            --  The expression must not be of a limited type; RM 4.3.1(17.4/5)

            if Is_Limited_Type (Etype (Expression (Assoc))) then
               Error_Msg_N
                 ("expression of a limited type in record delta aggregate " &
                    "is not allowed",
                  Expression (Assoc));
            end if;
         end if;

         Next (Assoc);
      end loop;

      declare
         type Choice_Info is record
            Choice : Node_Id;
            Depth  : Natural; -- 0 indicates non-record selector
         end record;

         Info          : array (1 .. Choice_Count) of Choice_Info;
         Current_Index : Natural := 0;

         function Choice_Depth (Choice : Node_Id) return Natural;
         --  Given a choice in record delta aggregate, return 1 for
         --  "Abc", 3 for "Aa.Bb.Cc", and 0 if anything other than
         --  record component selectors are involved.

         procedure Check_For_Bad_Overlap (Info1, Info2 : Choice_Info);
         --  If the two choices overlap illegally, then generate an error
         --  message. If deep delta aggregates are not enabled, then choices
         --  should be N_Identifier nodes and depths should each be 1.

         ------------------
         -- Choice_Depth --
         ------------------

         function Choice_Depth (Choice : Node_Id) return Natural is
            Prefix_Depth : Natural;
         begin
            case Nkind (Choice) is
               when N_Identifier =>
                  return 1;
               when N_Selected_Component =>
                  Prefix_Depth := Choice_Depth (Prefix (Choice));
                  if Prefix_Depth = 0 then
                     return 0;
                  else
                     return Prefix_Depth + 1;
                  end if;
               when others =>
                  return 0;
            end case;
         end Choice_Depth;

         ---------------------------
         -- Check_For_Bad_Overlap --
         ---------------------------

         procedure Check_For_Bad_Overlap (Info1, Info2 : Choice_Info) is
            Choice1, Choice2 : Node_Id;
         begin
            if Info1.Depth = 0 or Info2.Depth = 0 then
               --  We're not interested in cases involving array indexing
               return;
            end if;
            if Info1.Depth > Info2.Depth then
               --  Normalize
               Check_For_Bad_Overlap (Info1 => Info2, Info2 => Info1);
               return;
            end if;
            pragma Assert (Info1.Depth <= Info2.Depth);
            Choice1 := Info1.Choice;
            Choice2 := Info2.Choice;

            --  Adjust deeper choice to match depth of the other choice
            for Count in 1 .. Info2.Depth - Info1.Depth loop
               pragma Assert (Nkind (Choice2) = N_Selected_Component);
               Choice2 := Prefix (Choice2);
            end loop;

            --  Traverse the two choices; return if Entity mismatch found.
            loop
               pragma Assert (Nkind (Choice1) = Nkind (Choice2));
               if Nkind (Choice1) = N_Identifier then
                  exit when Entity (Choice1) = Entity (Choice2);
                  return; -- no overlap if entities differ
               end if;
               if Entity (Selector_Name (Choice1)) /=
                  Entity (Selector_Name (Choice2))
               then
                  return; -- no overlap if selected entities differ
               end if;
               Choice1 := Prefix (Choice1);
               Choice2 := Prefix (Choice2);
            end loop;

            --  Illegal overlap detected
            Error_Msg_Sloc := Sloc (Info2.Choice);
            Error_Msg_NE
              ("record delta aggregate choice overlaps with choice & #",
               Info1.Choice, Info2.Choice);
         end Check_For_Bad_Overlap;

      begin
         Assoc := First (Deltas);
         while Present (Assoc) loop
            Choice := First (Choice_List (Assoc));
            while Present (Choice) loop
               Current_Index := Current_Index + 1;
               Info (Current_Index) := (Choice => Choice,
                                        Depth => Choice_Depth (Choice));

               --  Check against previous Info elements
               for Prev_Index in 1 .. Current_Index - 1 loop
                  Check_For_Bad_Overlap
                    (Info (Prev_Index), Info (Current_Index));
               end loop;

               Next (Choice);
            end loop;
            Next (Assoc);
         end loop;
      end;
   end Resolve_Delta_Record_Aggregate;

   ------------------------------
   -- Resolve_Deep_Delta_Assoc --
   ------------------------------

   procedure Resolve_Deep_Delta_Assoc (N : Node_Id; Typ : Entity_Id) is
      Choice         : constant Node_Id := First (Choice_List (N));
      Enclosing_Type : Entity_Id := Typ;

      procedure Resolve_Choice_Prefix
        (Choice_Prefix : Node_Id; Enclosing_Type : in out Entity_Id);
      --  Recursively analyze selectors. Enclosing_Type is set to
      --  type of the last component.

      ---------------------------
      -- Resolve_Choice_Prefix --
      ---------------------------

      procedure Resolve_Choice_Prefix
        (Choice_Prefix : Node_Id; Enclosing_Type : in out Entity_Id)
      is
         Selector : Node_Id := Choice_Prefix;
      begin
         if not Is_Root_Prefix_Of_Deep_Choice (Choice_Prefix) then
            Resolve_Choice_Prefix (Prefix (Choice_Prefix), Enclosing_Type);

            if Nkind (Choice_Prefix) = N_Selected_Component then
               Selector := Selector_Name (Choice_Prefix);
            else
               pragma Assert (Nkind (Choice_Prefix) = N_Indexed_Component);
               Selector := First (Expressions (Choice_Prefix));
            end if;
         end if;

         if Is_Array_Type (Enclosing_Type) then
            Analyze_And_Resolve (Selector,
                                 Etype (First_Index (Enclosing_Type)));
            Enclosing_Type := Component_Type (Enclosing_Type);
         else
            declare
               Comp : Entity_Id := First_Entity (Enclosing_Type);
               Found : Boolean := False;
            begin
               while Present (Comp) and not Found loop
                  if Chars (Comp) = Chars (Selector) then
                     if Ekind (Comp) = E_Discriminant then
                        Error_Msg_N ("delta cannot apply to discriminant",
                                     Selector);
                     end if;
                     Found := True;
                     Set_Entity (Selector, Comp);
                     Set_Etype (Selector, Etype (Comp));
                     Set_Analyzed (Selector);
                     Enclosing_Type := Etype (Comp);
                  else
                     Next_Entity (Comp);
                  end if;
               end loop;
               if not Found then
                  Error_Msg_NE
                    ("type& has no component with this name",
                     Selector, Enclosing_Type);
               end if;
            end;
         end if;

         --  Set the type of the prefix for GNATprove, except for the root
         --  prefix, whose type is already the expected one for a record
         --  delta aggregate, or the type of the array index for an
         --  array delta aggregate (the only case here really since
         --  Resolve_Deep_Delta_Assoc is only called for array delta
         --  aggregates).

         if Selector /= Choice_Prefix then
            Set_Etype (Choice_Prefix, Enclosing_Type);
         end if;
      end Resolve_Choice_Prefix;
   begin
      declare
         Unimplemented : exception; -- TEMPORARY
      begin
         if Present (Next (Choice)) then
            raise Unimplemented;
         end if;
      end;

      Resolve_Choice_Prefix (Choice, Enclosing_Type);
      Analyze_And_Resolve (Expression (N), Enclosing_Type);
   end Resolve_Deep_Delta_Assoc;

   ---------------------------------
   -- Resolve_Extension_Aggregate --
   ---------------------------------

   --  There are two cases to consider:

   --  a) If the ancestor part is a type mark, the components needed are the
   --  difference between the components of the expected type and the
   --  components of the given type mark.

   --  b) If the ancestor part is an expression, it must be unambiguous, and
   --  once we have its type we can also compute the needed components as in
   --  the previous case. In both cases, if the ancestor type is not the
   --  immediate ancestor, we have to build this ancestor recursively.

   --  In both cases, discriminants of the ancestor type do not play a role in
   --  the resolution of the needed components, because inherited discriminants
   --  cannot be used in a type extension. As a result we can compute
   --  independently the list of components of the ancestor type and of the
   --  expected type.

   procedure Resolve_Extension_Aggregate (N : Node_Id; Typ : Entity_Id) is
      A      : constant Node_Id := Ancestor_Part (N);
      A_Type : Entity_Id;
      I      : Interp_Index;
      It     : Interp;

      function Valid_Limited_Ancestor (Anc : Node_Id) return Boolean;
      --  If the type is limited, verify that the ancestor part is a legal
      --  expression (aggregate or function call, including 'Input)) that does
      --  not require a copy, as specified in 7.5(2).

      function Valid_Ancestor_Type return Boolean;
      --  Verify that the type of the ancestor part is a non-private ancestor
      --  of the expected type, which must be a type extension.

      ----------------------------
      -- Valid_Limited_Ancestor --
      ----------------------------

      function Valid_Limited_Ancestor (Anc : Node_Id) return Boolean is
      begin
         if Is_Entity_Name (Anc) and then Is_Type (Entity (Anc)) then
            return True;

         --  The ancestor must be a call or an aggregate, but a call may
         --  have been expanded into a temporary, so check original node.

         elsif Nkind (Anc) in N_Aggregate
                            | N_Extension_Aggregate
                            | N_Function_Call
         then
            return True;

         elsif Nkind (Original_Node (Anc)) = N_Function_Call then
            return True;

         elsif Nkind (Anc) = N_Attribute_Reference
           and then Attribute_Name (Anc) = Name_Input
         then
            return True;

         elsif Nkind (Anc) = N_Qualified_Expression then
            return Valid_Limited_Ancestor (Expression (Anc));

         elsif Nkind (Anc) = N_Raise_Expression then
            return True;

         else
            return False;
         end if;
      end Valid_Limited_Ancestor;

      -------------------------
      -- Valid_Ancestor_Type --
      -------------------------

      function Valid_Ancestor_Type return Boolean is
         Imm_Type : Entity_Id;

      begin
         Imm_Type := Base_Type (Typ);
         while Is_Derived_Type (Imm_Type) loop
            if Etype (Imm_Type) = Base_Type (A_Type) then
               return True;

            --  The base type of the parent type may appear as a private
            --  extension if it is declared as such in a parent unit of the
            --  current one. For consistency of the subsequent analysis use
            --  the partial view for the ancestor part.

            elsif Is_Private_Type (Etype (Imm_Type))
              and then Present (Full_View (Etype (Imm_Type)))
              and then Base_Type (A_Type) = Full_View (Etype (Imm_Type))
            then
               A_Type := Etype (Imm_Type);
               return True;

            --  The parent type may be a private extension. The aggregate is
            --  legal if the type of the aggregate is an extension of it that
            --  is not a private extension.

            elsif Is_Private_Type (A_Type)
              and then not Is_Private_Type (Imm_Type)
              and then Present (Full_View (A_Type))
              and then Base_Type (Full_View (A_Type)) = Etype (Imm_Type)
            then
               return True;

            --  The parent type may be a raise expression (which is legal in
            --  any expression context).

            elsif A_Type = Raise_Type then
               A_Type := Etype (Imm_Type);
               return True;

            else
               Imm_Type := Etype (Base_Type (Imm_Type));
            end if;
         end loop;

         --  If previous loop did not find a proper ancestor, report error

         Error_Msg_NE ("expect ancestor type of &", A, Typ);
         return False;
      end Valid_Ancestor_Type;

   --  Start of processing for Resolve_Extension_Aggregate

   begin
      --  Analyze the ancestor part and account for the case where it is a
      --  parameterless function call.

      Analyze (A);
      Check_Parameterless_Call (A);

      if Is_Entity_Name (A) and then Is_Type (Entity (A)) then

         --  AI05-0115: If the ancestor part is a subtype mark, the ancestor
         --  must not have unknown discriminants. To catch cases where the
         --  aggregate occurs at a place where the full view of the ancestor
         --  type is visible and doesn't have unknown discriminants, but the
         --  aggregate type was derived from a partial view that has unknown
         --  discriminants, we check whether the aggregate type has unknown
         --  discriminants (unknown discriminants were inherited), along
         --  with checking that the partial view of the ancestor has unknown
         --  discriminants. (It might be sufficient to replace the entire
         --  condition with Has_Unknown_Discriminants (Typ), but that might
         --  miss some cases, not clear, and causes error changes in some tests
         --  such as class-wide cases, that aren't clearly improvements. ???)

         if Has_Unknown_Discriminants (Entity (A))
           or else (Has_Unknown_Discriminants (Typ)
                      and then Partial_View_Has_Unknown_Discr (Entity (A)))
         then
            Error_Msg_NE
              ("aggregate not available for type& whose ancestor "
                 & "has unknown discriminants", N, Typ);
         end if;
      end if;

      if not Is_Tagged_Type (Typ) then
         Error_Msg_N ("type of extension aggregate must be tagged", N);
         return;

      elsif Is_Limited_Type (Typ) then

         --  Ada 2005 (AI-287): Limited aggregates are allowed

         if Ada_Version < Ada_2005 then
            Error_Msg_N ("aggregate type cannot be limited", N);
            Explain_Limited_Type (Typ, N);
            return;

         elsif Valid_Limited_Ancestor (A) then
            null;

         else
            Error_Msg_N
              ("limited ancestor part must be aggregate or function call", A);
         end if;

      elsif Is_Class_Wide_Type (Typ) then
         Error_Msg_N ("aggregate cannot be of a class-wide type", N);
         return;
      end if;

      if Is_Entity_Name (A) and then Is_Type (Entity (A)) then
         A_Type := Get_Full_View (Entity (A));

         if Valid_Ancestor_Type then
            Set_Entity (A, A_Type);
            Set_Etype  (A, A_Type);

            Validate_Ancestor_Part (N);
            Resolve_Record_Aggregate (N, Typ);
         end if;

      elsif Nkind (A) /= N_Aggregate then
         if Is_Overloaded (A) then
            A_Type := Any_Type;

            Get_First_Interp (A, I, It);
            while Present (It.Typ) loop

               --  Consider limited interpretations if Ada 2005 or higher

               if Is_Tagged_Type (It.Typ)
                 and then (Ada_Version >= Ada_2005
                            or else not Is_Limited_Type (It.Typ))
               then
                  if A_Type /= Any_Type then
                     Error_Msg_N ("cannot resolve expression", A);
                     return;
                  else
                     A_Type := It.Typ;
                  end if;
               end if;

               Get_Next_Interp (I, It);
            end loop;

            if A_Type = Any_Type then
               if Ada_Version >= Ada_2005 then
                  Error_Msg_N
                    ("ancestor part must be of a tagged type", A);
               else
                  Error_Msg_N
                    ("ancestor part must be of a nonlimited tagged type", A);
               end if;

               return;
            end if;

         else
            A_Type := Etype (A);
         end if;

         if Valid_Ancestor_Type then
            Resolve (A, A_Type);
            Check_Unset_Reference (A);
            Check_Non_Static_Context (A);

            --  The aggregate is illegal if the ancestor expression is a call
            --  to a function with a limited unconstrained result, unless the
            --  type of the aggregate is a null extension. This restriction
            --  was added in AI05-67 to simplify implementation.

            if Nkind (A) = N_Function_Call
              and then Is_Limited_Type (A_Type)
              and then not Is_Null_Extension (Typ)
              and then not Is_Constrained (A_Type)
            then
               Error_Msg_N
                 ("type of limited ancestor part must be constrained", A);

            --  Reject the use of CPP constructors that leave objects partially
            --  initialized. For example:

            --    type CPP_Root is tagged limited record ...
            --    pragma Import (CPP, CPP_Root);

            --    type CPP_DT is new CPP_Root and Iface ...
            --    pragma Import (CPP, CPP_DT);

            --    type Ada_DT is new CPP_DT with ...

            --    Obj : Ada_DT := Ada_DT'(New_CPP_Root with others => <>);

            --  Using the constructor of CPP_Root the slots of the dispatch
            --  table of CPP_DT cannot be set, and the secondary tag of
            --  CPP_DT is unknown.

            elsif Nkind (A) = N_Function_Call
              and then Is_CPP_Constructor_Call (A)
              and then Enclosing_CPP_Parent (Typ) /= A_Type
            then
               Error_Msg_NE
                 ("??must use 'C'P'P constructor for type &", A,
                  Enclosing_CPP_Parent (Typ));

               --  The following call is not needed if the previous warning
               --  is promoted to an error.

               Resolve_Record_Aggregate (N, Typ);

            elsif Is_Class_Wide_Type (Etype (A))
              and then Nkind (Original_Node (A)) = N_Function_Call
            then
               --  If the ancestor part is a dispatching call, it appears
               --  statically to be a legal ancestor, but it yields any member
               --  of the class, and it is not possible to determine whether
               --  it is an ancestor of the extension aggregate (much less
               --  which ancestor). It is not possible to determine the
               --  components of the extension part.

               --  This check implements AI-306, which in fact was motivated by
               --  an AdaCore query to the ARG after this test was added.

               Error_Msg_N ("ancestor part must be statically tagged", A);

            else
               Resolve_Record_Aggregate (N, Typ);
            end if;
         end if;

      else
         Error_Msg_N ("no unique type for this aggregate", A);
      end if;

      Check_Function_Writable_Actuals (N);
   end Resolve_Extension_Aggregate;

   ----------------------------------
   -- Resolve_Null_Array_Aggregate --
   ----------------------------------

   function Resolve_Null_Array_Aggregate (N : Node_Id) return Boolean is
      --  Never returns False, but declared as a function to match
      --  other Resolve_Mumble functions.

      Loc    : constant Source_Ptr := Sloc (N);
      Typ    : constant Entity_Id := Etype (N);

      Constr       : constant List_Id := New_List;
      Index        : Node_Id;
      Index_Typ    : Node_Id;
      Known_Bounds : Boolean := True;
      Lo, Hi       : Node_Id;

   begin
      --  Attach the list of constraints at the location of the aggregate, so
      --  the individual constraints can be analyzed.

      Set_Parent (Constr, N);

      --  Populate the list with null ranges. The relevant RM clauses are
      --  RM 4.3.3 (26.1) and RM 4.3.3 (26).

      Index := First_Index (Typ);
      while Present (Index) loop
         Get_Index_Bounds (Index, L => Lo, H => Hi);
         Index_Typ := Etype (Index);

         Known_Bounds := Known_Bounds
           and Compile_Time_Known_Value (Lo)
           and Compile_Time_Known_Value (Hi);

         if Cannot_Compute_High_Bound (Index) then
            --  The upper bound is the higger bound to avoid reporting
            --  spurious errors; this value will not be used at runtime
            --  because this aggregate will be replaced by a raise CE node,
            --  or the index type is formal of a generic unit.

            Hi := New_Copy_Tree (Lo);

            Report_Null_Array_Constraint_Error (N, Index_Typ);
            Set_Raises_Constraint_Error (N);

         else
            --  The upper bound is the predecessor of the lower bound

            Hi := Make_Attribute_Reference (Loc,
                    Prefix         => New_Occurrence_Of (Etype (Index), Loc),
                    Attribute_Name => Name_Pred,
                    Expressions    => New_List (New_Copy_Tree (Lo)));
         end if;

         Append (Make_Range (Loc, New_Copy_Tree (Lo), Hi), Constr);
         Analyze_And_Resolve (Last (Constr), Etype (Index));

         Next_Index (Index);
      end loop;

      Set_Compile_Time_Known_Aggregate (N, Known_Bounds);
      Set_Aggregate_Bounds (N, First (Constr));

      return True;
   end Resolve_Null_Array_Aggregate;

   ------------------------------
   -- Resolve_Record_Aggregate --
   ------------------------------

   procedure Resolve_Record_Aggregate (N : Node_Id; Typ : Entity_Id) is
      New_Assoc_List : constant List_Id := New_List;
      --  New_Assoc_List is the newly built list of N_Component_Association
      --  nodes.

      Others_Etype : Entity_Id := Empty;
      --  This variable is used to save the Etype of the last record component
      --  that takes its value from the others choice. Its purpose is:
      --
      --    (a) make sure the others choice is useful
      --
      --    (b) make sure the type of all the components whose value is
      --        subsumed by the others choice are the same.
      --
      --  This variable is updated as a side effect of function Get_Value.

      Box_Node               : Node_Id := Empty;
      Is_Box_Present         : Boolean := False;
      Is_Box_Init_By_Default : Boolean := False;
      Others_Box             : Natural := 0;
      --  Ada 2005 (AI-287): Variables used in case of default initialization
      --  to provide a functionality similar to Others_Etype. Box_Present
      --  indicates that the component takes its default initialization;
      --  Others_Box counts the number of components of the current aggregate
      --  (which may be a sub-aggregate of a larger one) that are default-
      --  initialized. A value of One indicates that an others_box is present.
      --  Any larger value indicates that the others_box is not redundant.
      --  These variables, similar to Others_Etype, are also updated as a side
      --  effect of function Get_Value. Box_Node is used to place a warning on
      --  a redundant others_box.

      procedure Add_Association
        (Component      : Entity_Id;
         Expr           : Node_Id;
         Assoc_List     : List_Id;
         Is_Box_Present : Boolean := False);
      --  Builds a new N_Component_Association node which associates Component
      --  to expression Expr and adds it to the association list being built,
      --  either New_Assoc_List, or the association being built for an inner
      --  aggregate.

      function Discriminant_Present (Input_Discr : Entity_Id) return Boolean;
      --  If aggregate N is a regular aggregate this routine will return True.
      --  Otherwise, if N is an extension aggregate, then Input_Discr denotes
      --  a discriminant whose value may already have been specified by N's
      --  ancestor part. This routine checks whether this is indeed the case
      --  and if so returns False, signaling that no value for Input_Discr
      --  should appear in N's aggregate part. Also, in this case, the routine
      --  appends to New_Assoc_List the discriminant value specified in the
      --  ancestor part.
      --
      --  If the aggregate is in a context with expansion delayed, it will be
      --  reanalyzed. The inherited discriminant values must not be reinserted
      --  in the component list to prevent spurious errors, but they must be
      --  present on first analysis to build the proper subtype indications.
      --  The flag Inherited_Discriminant is used to prevent the re-insertion.

      function Find_Private_Ancestor (Typ : Entity_Id) return Entity_Id;
      --  AI05-0115: Find earlier ancestor in the derivation chain that is
      --  derived from private view Typ. Whether the aggregate is legal depends
      --  on the current visibility of the type as well as that of the parent
      --  of the ancestor.

      function Get_Value
        (Compon                 : Entity_Id;
         From                   : List_Id;
         Consider_Others_Choice : Boolean := False) return Node_Id;
      --  Given a record component stored in parameter Compon, this function
      --  returns its value as it appears in the list From, which is a list
      --  of N_Component_Association nodes.
      --
      --  If no component association has a choice for the searched component,
      --  the value provided by the others choice is returned, if there is one,
      --  and Consider_Others_Choice is set to true. Otherwise Empty is
      --  returned. If there is more than one component association giving a
      --  value for the searched record component, an error message is emitted
      --  and the first found value is returned.
      --
      --  If Consider_Others_Choice is set and the returned expression comes
      --  from the others choice, then Others_Etype is set as a side effect.
      --  An error message is emitted if the components taking their value from
      --  the others choice do not have same type.

      procedure Resolve_Aggr_Expr (Expr : Node_Id; Component : Entity_Id);
      --  Analyzes and resolves expression Expr against the Etype of the
      --  Component. This routine also applies all appropriate checks to Expr.
      --  It finally saves a Expr in the newly created association list that
      --  will be attached to the final record aggregate. Note that if the
      --  Parent pointer of Expr is not set then Expr was produced with a
      --  New_Copy_Tree or some such.

      procedure Rewrite_Range (Root_Type : Entity_Id; Rge : Node_Id);
      --  Rewrite a range node Rge when its bounds refer to non-stored
      --  discriminants from Root_Type, to replace them with the stored
      --  discriminant values. This is required in GNATprove mode, and is
      --  adopted in all modes to avoid special-casing GNATprove mode.

      ---------------------
      -- Add_Association --
      ---------------------

      procedure Add_Association
        (Component      : Entity_Id;
         Expr           : Node_Id;
         Assoc_List     : List_Id;
         Is_Box_Present : Boolean := False)
      is
         Choice_List : constant List_Id := New_List;
         Loc         : Source_Ptr;

      begin
         --  If this is a box association the expression is missing, so use the
         --  Sloc of the aggregate itself for the new association.

         pragma Assert (Present (Expr) xor Is_Box_Present);

         if Present (Expr) then
            Loc := Sloc (Expr);
         else
            Loc := Sloc (N);
         end if;

         Append_To (Choice_List, New_Occurrence_Of (Component, Loc));

         Append_To (Assoc_List,
           Make_Component_Association (Loc,
             Choices     => Choice_List,
             Expression  => Expr,
             Box_Present => Is_Box_Present));

         --  If this association has a box for a component that is initialized
         --  by default, then set flag on the new association to indicate that
         --  the original association was for such a box-initialized component.

         if Is_Box_Init_By_Default then
            Set_Was_Default_Init_Box_Association (Last (Assoc_List));
         end if;
      end Add_Association;

      --------------------------
      -- Discriminant_Present --
      --------------------------

      function Discriminant_Present (Input_Discr : Entity_Id) return Boolean is
         Regular_Aggr : constant Boolean := Nkind (N) /= N_Extension_Aggregate;

         Ancestor_Is_Subtyp : Boolean;

         Loc : Source_Ptr;

         Ancestor     : Node_Id;
         Ancestor_Typ : Entity_Id;
         Comp_Assoc   : Node_Id;
         Discr        : Entity_Id;
         Discr_Expr   : Node_Id;
         Discr_Val    : Elmt_Id := No_Elmt;
         Orig_Discr   : Entity_Id;

      begin
         if Regular_Aggr then
            return True;
         end if;

         --  Check whether inherited discriminant values have already been
         --  inserted in the aggregate. This will be the case if we are
         --  re-analyzing an aggregate whose expansion was delayed.

         if Present (Component_Associations (N)) then
            Comp_Assoc := First (Component_Associations (N));
            while Present (Comp_Assoc) loop
               if Inherited_Discriminant (Comp_Assoc) then
                  return True;
               end if;

               Next (Comp_Assoc);
            end loop;
         end if;

         Ancestor     := Ancestor_Part (N);
         Ancestor_Typ := Etype (Ancestor);
         Loc          := Sloc (Ancestor);

         --  For a private type with unknown discriminants, use the underlying
         --  record view if it is available.

         if Has_Unknown_Discriminants (Ancestor_Typ)
           and then Present (Full_View (Ancestor_Typ))
           and then Present (Underlying_Record_View (Full_View (Ancestor_Typ)))
         then
            Ancestor_Typ := Underlying_Record_View (Full_View (Ancestor_Typ));
         end if;

         Ancestor_Is_Subtyp :=
           Is_Entity_Name (Ancestor) and then Is_Type (Entity (Ancestor));

         --  If the ancestor part has no discriminants clearly N's aggregate
         --  part must provide a value for Discr.

         if not Has_Discriminants (Ancestor_Typ) then
            return True;

         --  If the ancestor part is an unconstrained subtype mark then the
         --  Discr must be present in N's aggregate part.

         elsif Ancestor_Is_Subtyp
           and then not Is_Constrained (Entity (Ancestor))
         then
            return True;
         end if;

         --  Now look to see if Discr was specified in the ancestor part

         if Ancestor_Is_Subtyp then
            Discr_Val :=
              First_Elmt (Discriminant_Constraint (Entity (Ancestor)));
         end if;

         Orig_Discr := Original_Record_Component (Input_Discr);

         Discr := First_Discriminant (Ancestor_Typ);
         while Present (Discr) loop

            --  If Ancestor has already specified Disc value then insert its
            --  value in the final aggregate.

            if Original_Record_Component (Discr) = Orig_Discr then
               if Ancestor_Is_Subtyp then
                  Discr_Expr := New_Copy_Tree (Node (Discr_Val));
               else
                  Discr_Expr :=
                    Make_Selected_Component (Loc,
                      Prefix        => Duplicate_Subexpr (Ancestor),
                      Selector_Name => New_Occurrence_Of (Input_Discr, Loc));
               end if;

               Resolve_Aggr_Expr (Discr_Expr, Input_Discr);
               Set_Inherited_Discriminant (Last (New_Assoc_List));
               return False;
            end if;

            Next_Discriminant (Discr);

            if Ancestor_Is_Subtyp then
               Next_Elmt (Discr_Val);
            end if;
         end loop;

         return True;
      end Discriminant_Present;

      ---------------------------
      -- Find_Private_Ancestor --
      ---------------------------

      function Find_Private_Ancestor (Typ : Entity_Id) return Entity_Id is
         Par : Entity_Id;

      begin
         Par := Typ;
         loop
            if Has_Private_Ancestor (Par)
              and then not Has_Private_Ancestor (Etype (Base_Type (Par)))
            then
               return Par;

            elsif not Is_Derived_Type (Par) then
               return Empty;

            else
               Par := Etype (Base_Type (Par));
            end if;
         end loop;
      end Find_Private_Ancestor;

      ---------------
      -- Get_Value --
      ---------------

      function Get_Value
        (Compon                 : Entity_Id;
         From                   : List_Id;
         Consider_Others_Choice : Boolean := False) return Node_Id
      is
         Typ           : constant Entity_Id := Etype (Compon);
         Assoc         : Node_Id;
         Expr          : Node_Id := Empty;
         Selector_Name : Node_Id;

      begin
         Is_Box_Present := False;
         Is_Box_Init_By_Default := False;

         if No (From) then
            return Empty;
         end if;

         Assoc := First (From);
         while Present (Assoc) loop
            Selector_Name := First (Choices (Assoc));
            while Present (Selector_Name) loop
               if Nkind (Selector_Name) = N_Others_Choice then
                  if Consider_Others_Choice and then No (Expr) then

                     --  We need to duplicate the expression for each
                     --  successive component covered by the others choice.
                     --  This is redundant if the others_choice covers only
                     --  one component (small optimization possible???), but
                     --  indispensable otherwise, because each one must be
                     --  expanded individually to preserve side effects.

                     --  Ada 2005 (AI-287): In case of default initialization
                     --  of components, we duplicate the corresponding default
                     --  expression (from the record type declaration). The
                     --  copy must carry the sloc of the association (not the
                     --  original expression) to prevent spurious elaboration
                     --  checks when the default includes function calls.

                     if Box_Present (Assoc) then
                        Others_Box     := Others_Box + 1;
                        Is_Box_Present := True;

                        if Expander_Active then
                           return
                             New_Copy_Tree_And_Copy_Dimensions
                               (Expression (Parent (Compon)),
                                New_Sloc => Sloc (Assoc));
                        else
                           return Expression (Parent (Compon));
                        end if;

                     else
                        if Present (Others_Etype)
                          and then Base_Type (Others_Etype) /= Base_Type (Typ)
                        then
                           --  If the components are of an anonymous access
                           --  type they are distinct, but this is legal in
                           --  Ada 2012 as long as designated types match.

                           if (Ekind (Typ) = E_Anonymous_Access_Type
                                or else Ekind (Typ) =
                                            E_Anonymous_Access_Subprogram_Type)
                             and then Designated_Type (Typ) =
                                            Designated_Type (Others_Etype)
                           then
                              null;
                           else
                              Error_Msg_N
                                ("components in OTHERS choice must have same "
                                 & "type", Selector_Name);
                           end if;
                        end if;

                        Others_Etype := Typ;

                        --  Copy the expression so that it is resolved
                        --  independently for each component, This is needed
                        --  for accessibility checks on components of anonymous
                        --  access types, even in compile_only mode.

                        if not Inside_A_Generic then
                           return
                             New_Copy_Tree_And_Copy_Dimensions
                               (Expression (Assoc));
                        else
                           return Expression (Assoc);
                        end if;
                     end if;
                  end if;

               elsif Chars (Compon) = Chars (Selector_Name) then
                  if No (Expr) then

                     --  Ada 2005 (AI-231)

                     if Ada_Version >= Ada_2005
                       and then Known_Null (Expression (Assoc))
                     then
                        Check_Can_Never_Be_Null (Compon, Expression (Assoc));
                     end if;

                     --  We need to duplicate the expression when several
                     --  components are grouped together with a "|" choice.
                     --  For instance "filed1 | filed2 => Expr"

                     --  Ada 2005 (AI-287)

                     if Box_Present (Assoc) then
                        Is_Box_Present := True;

                        --  Duplicate the default expression of the component
                        --  from the record type declaration, so a new copy
                        --  can be attached to the association.

                        --  Note that we always copy the default expression,
                        --  even when the association has a single choice, in
                        --  order to create a proper association for the
                        --  expanded aggregate.

                        --  Component may have no default, in which case the
                        --  expression is empty and the component is default-
                        --  initialized, but an association for the component
                        --  exists, and it is not covered by an others clause.

                        --  Scalar and private types have no initialization
                        --  procedure, so they remain uninitialized. If the
                        --  target of the aggregate is a constant this
                        --  deserves a warning.

                        if No (Expression (Parent (Compon)))
                          and then not Has_Non_Null_Base_Init_Proc (Typ)
                          and then not Has_Aspect (Typ, Aspect_Default_Value)
                          and then not Is_Concurrent_Type (Typ)
                          and then Nkind (Parent (N)) = N_Object_Declaration
                          and then Constant_Present (Parent (N))
                        then
                           Error_Msg_Node_2 := Typ;
                           Error_Msg_NE
                             ("??component& of type& is uninitialized",
                              Assoc, Selector_Name);

                           --  An additional reminder if the component type
                           --  is a generic formal.

                           if Is_Generic_Type (Base_Type (Typ)) then
                              Error_Msg_NE
                                ("\instance should provide actual type with "
                                 & "initialization for&", Assoc, Typ);
                           end if;
                        end if;

                        return
                          New_Copy_Tree_And_Copy_Dimensions
                            (Expression (Parent (Compon)));

                     else
                        if Present (Next (Selector_Name)) then
                           Expr := New_Copy_Tree_And_Copy_Dimensions
                                     (Expression (Assoc));
                        else
                           Expr := Expression (Assoc);
                        end if;
                     end if;

                     Generate_Reference (Compon, Selector_Name, 'm');

                  else
                     Error_Msg_NE
                       ("more than one value supplied for &",
                        Selector_Name, Compon);

                  end if;
               end if;

               Next (Selector_Name);
            end loop;

            Next (Assoc);
         end loop;

         return Expr;
      end Get_Value;

      -----------------------
      -- Resolve_Aggr_Expr --
      -----------------------

      procedure Resolve_Aggr_Expr (Expr : Node_Id; Component : Entity_Id) is
         function Has_Expansion_Delayed (Expr : Node_Id) return Boolean;
         --  If the expression is an aggregate (possibly qualified) then its
         --  expansion is delayed until the enclosing aggregate is expanded
         --  into assignments. In that case, do not generate checks on the
         --  expression, because they will be generated later, and will other-
         --  wise force a copy (to remove side effects) that would leave a
         --  dynamic-sized aggregate in the code, something that gigi cannot
         --  handle.

         ---------------------------
         -- Has_Expansion_Delayed --
         ---------------------------

         function Has_Expansion_Delayed (Expr : Node_Id) return Boolean is
         begin
            return
               (Nkind (Expr) in N_Aggregate | N_Extension_Aggregate
                 and then Present (Etype (Expr))
                 and then Is_Record_Type (Etype (Expr))
                 and then Expansion_Delayed (Expr))
              or else
                (Nkind (Expr) = N_Qualified_Expression
                  and then Has_Expansion_Delayed (Expression (Expr)));
         end Has_Expansion_Delayed;

         --  Local variables

         Expr_Type : Entity_Id := Empty;
         New_C     : Entity_Id := Component;
         New_Expr  : Node_Id;

         Relocate : Boolean;
         --  Set to True if the resolved Expr node needs to be relocated when
         --  attached to the newly created association list. This node need not
         --  be relocated if its parent pointer is not set. In fact in this
         --  case Expr is the output of a New_Copy_Tree call. If Relocate is
         --  True then we have analyzed the expression node in the original
         --  aggregate and hence it needs to be relocated when moved over to
         --  the new association list.

      --  Start of processing for Resolve_Aggr_Expr

      begin
         --  If the type of the component is elementary or the type of the
         --  aggregate does not contain discriminants, use the type of the
         --  component to resolve Expr.

         if Is_Elementary_Type (Etype (Component))
           or else not Has_Discriminants (Etype (N))
         then
            Expr_Type := Etype (Component);

         --  Otherwise we have to pick up the new type of the component from
         --  the new constrained subtype of the aggregate. In fact components
         --  which are of a composite type might be constrained by a
         --  discriminant, and we want to resolve Expr against the subtype were
         --  all discriminant occurrences are replaced with their actual value.

         else
            New_C := First_Component (Etype (N));
            while Present (New_C) loop
               if Chars (New_C) = Chars (Component) then
                  Expr_Type := Etype (New_C);
                  exit;
               end if;

               Next_Component (New_C);
            end loop;

            pragma Assert (Present (Expr_Type));

            --  For each range in an array type where a discriminant has been
            --  replaced with the constraint, check that this range is within
            --  the range of the base type. This checks is done in the init
            --  proc for regular objects, but has to be done here for
            --  aggregates since no init proc is called for them.

            if Is_Array_Type (Expr_Type) then
               declare
                  Index : Node_Id;
                  --  Range of the current constrained index in the array

                  Orig_Index : Node_Id := First_Index (Etype (Component));
                  --  Range corresponding to the range Index above in the
                  --  original unconstrained record type. The bounds of this
                  --  range may be governed by discriminants.

                  Unconstr_Index : Node_Id := First_Index (Etype (Expr_Type));
                  --  Range corresponding to the range Index above for the
                  --  unconstrained array type. This range is needed to apply
                  --  range checks.

               begin
                  Index := First_Index (Expr_Type);
                  while Present (Index) loop
                     if Depends_On_Discriminant (Orig_Index) then
                        Apply_Range_Check (Index, Etype (Unconstr_Index));
                     end if;

                     Next_Index (Index);
                     Next_Index (Orig_Index);
                     Next_Index (Unconstr_Index);
                  end loop;
               end;
            end if;
         end if;

         --  If the Parent pointer of Expr is not set, Expr is an expression
         --  duplicated by New_Tree_Copy (this happens for record aggregates
         --  that look like (Field1 | Filed2 => Expr) or (others => Expr)).
         --  Such a duplicated expression must be attached to the tree
         --  before analysis and resolution to enforce the rule that a tree
         --  fragment should never be analyzed or resolved unless it is
         --  attached to the current compilation unit.

         if No (Parent (Expr)) then
            Set_Parent (Expr, N);
            Relocate := False;
         else
            Relocate := True;
         end if;

         --  Obtain the corresponding mutably tagged types if we are looking
         --  at a special internally generated class-wide equivalent type.

         Expr_Type :=
           Get_Corresponding_Mutably_Tagged_Type_If_Present (Expr_Type);

         Analyze_And_Resolve (Expr, Expr_Type);
         Check_Expr_OK_In_Limited_Aggregate (Expr);
         Check_Non_Static_Context (Expr);
         Check_Unset_Reference (Expr);

         --  Check wrong use of class-wide types

         if Is_Class_Wide_Type (Etype (Expr))
           and then not Is_Mutably_Tagged_Type (Expr_Type)
         then
            Error_Msg_N ("dynamically tagged expression not allowed", Expr);
         end if;

         if not Has_Expansion_Delayed (Expr) then
            Aggregate_Constraint_Checks (Expr, Expr_Type);
         end if;

         --  If an aggregate component has a type with predicates, an explicit
         --  predicate check must be applied, as for an assignment statement,
         --  because the aggregate might not be expanded into individual
         --  component assignments.

         if Has_Predicates (Expr_Type)
           and then Analyzed (Expr)
         then
            Apply_Predicate_Check (Expr, Expr_Type);
         end if;

         if Raises_Constraint_Error (Expr) then
            Set_Raises_Constraint_Error (N);
         end if;

         --  If the expression has been marked as requiring a range check, then
         --  generate it here. It's a bit odd to be generating such checks in
         --  the analyzer, but harmless since Generate_Range_Check does nothing
         --  (other than making sure Do_Range_Check is set) if the expander is
         --  not active.

         if Do_Range_Check (Expr) then
            Generate_Range_Check (Expr, Expr_Type, CE_Range_Check_Failed);
         end if;

         --  Add association Component => Expr if the caller requests it

         if Relocate then
            New_Expr := Relocate_Node (Expr);

            --  Since New_Expr is not gonna be analyzed later on, we need to
            --  propagate here the dimensions form Expr to New_Expr.

            Copy_Dimensions (Expr, New_Expr);

         else
            New_Expr := Expr;
         end if;

         Add_Association (New_C, New_Expr, New_Assoc_List);
      end Resolve_Aggr_Expr;

      -------------------
      -- Rewrite_Range --
      -------------------

      procedure Rewrite_Range (Root_Type : Entity_Id; Rge : Node_Id) is
         procedure Rewrite_Bound
           (Bound     : Node_Id;
            Disc      : Entity_Id;
            Expr_Disc : Node_Id);
         --  Rewrite a bound of the range Bound, when it is equal to the
         --  non-stored discriminant Disc, into the stored discriminant
         --  value Expr_Disc.

         -------------------
         -- Rewrite_Bound --
         -------------------

         procedure Rewrite_Bound
           (Bound     : Node_Id;
            Disc      : Entity_Id;
            Expr_Disc : Node_Id)
         is
         begin
            if Nkind (Bound) /= N_Identifier then
               return;
            end if;

            --  We expect either the discriminant or the discriminal

            if Entity (Bound) = Disc
              or else (Ekind (Entity (Bound)) = E_In_Parameter
                        and then Discriminal_Link (Entity (Bound)) = Disc)
            then
               Rewrite (Bound, New_Copy_Tree (Expr_Disc));
            end if;
         end Rewrite_Bound;

         --  Local variables

         Low, High : Node_Id;
         Disc      : Entity_Id;
         Expr_Disc : Elmt_Id;

      --  Start of processing for Rewrite_Range

      begin
         if Has_Discriminants (Root_Type) and then Nkind (Rge) = N_Range then
            Low := Low_Bound (Rge);
            High := High_Bound (Rge);

            Disc      := First_Discriminant (Root_Type);
            Expr_Disc := First_Elmt (Stored_Constraint (Etype (N)));
            while Present (Disc) loop
               Rewrite_Bound (Low, Disc, Node (Expr_Disc));
               Rewrite_Bound (High, Disc, Node (Expr_Disc));
               Next_Discriminant (Disc);
               Next_Elmt (Expr_Disc);
            end loop;
         end if;
      end Rewrite_Range;

      --  Local variables

      Components : constant Elist_Id := New_Elmt_List;
      --  Components is the list of the record components whose value must be
      --  provided in the aggregate. This list does include discriminants.

      Component       : Entity_Id;
      Component_Elmt  : Elmt_Id;
      Expr            : Node_Id;
      Positional_Expr : Node_Id;

   --  Start of processing for Resolve_Record_Aggregate

   begin
      --  A record aggregate is restricted in SPARK:

      --    Each named association can have only a single choice.
      --    OTHERS cannot be used.
      --    Positional and named associations cannot be mixed.

      if Present (Component_Associations (N)) then
         declare
            Assoc : Node_Id;

         begin
            Assoc := First (Component_Associations (N));
            while Present (Assoc) loop
               if Nkind (Assoc) = N_Iterated_Component_Association then
                  Error_Msg_N
                    ("iterated component association can only appear in an "
                     & "array aggregate", N);
                  raise Unrecoverable_Error;
               end if;

               Next (Assoc);
            end loop;
         end;
      end if;

      --  We may end up calling Duplicate_Subexpr on expressions that are
      --  attached to New_Assoc_List. For this reason we need to attach it
      --  to the tree by setting its parent pointer to N. This parent point
      --  will change in STEP 8 below.

      Set_Parent (New_Assoc_List, N);

      --  STEP 1: abstract type and null record verification

      if Is_Abstract_Type (Typ) then
         Error_Msg_N ("type of aggregate cannot be abstract",  N);
      end if;

      if No (First_Entity (Typ)) and then Null_Record_Present (N) then
         Set_Etype (N, Typ);
         return;

      elsif Present (First_Entity (Typ))
        and then Null_Record_Present (N)
        and then not Is_Tagged_Type (Typ)
      then
         Error_Msg_N ("record aggregate cannot be null", N);
         return;

      --  If the type has no components, then the aggregate should either
      --  have "null record", or in Ada 2005 it could instead have a single
      --  component association given by "others => <>". For Ada 95 we flag an
      --  error at this point, but for Ada 2005 we proceed with checking the
      --  associations below, which will catch the case where it's not an
      --  aggregate with "others => <>". Note that the legality of a <>
      --  aggregate for a null record type was established by AI05-016.

      elsif No (First_Entity (Typ))
         and then Ada_Version < Ada_2005
      then
         Error_Msg_N ("record aggregate must be null", N);
         return;
      end if;

      --  STEP 2: Verify aggregate structure

      Step_2 : declare
         Assoc         : Node_Id;
         Bad_Aggregate : Boolean := False;
         Selector_Name : Node_Id;

      begin
         if Present (Component_Associations (N)) then
            Assoc := First (Component_Associations (N));
         else
            Assoc := Empty;
         end if;

         while Present (Assoc) loop
            Selector_Name := First (Choices (Assoc));
            while Present (Selector_Name) loop
               if Nkind (Selector_Name) = N_Identifier then
                  null;

               elsif Nkind (Selector_Name) = N_Others_Choice then
                  if Selector_Name /= First (Choices (Assoc))
                    or else Present (Next (Selector_Name))
                  then
                     Error_Msg_N
                       ("OTHERS must appear alone in a choice list",
                        Selector_Name);
                     return;

                  elsif Present (Next (Assoc)) then
                     Error_Msg_N
                       ("OTHERS must appear last in an aggregate",
                        Selector_Name);
                     return;

                  --  (Ada 2005): If this is an association with a box,
                  --  indicate that the association need not represent
                  --  any component.

                  elsif Box_Present (Assoc) then
                     Others_Box := 1;
                     Box_Node   := Assoc;
                  end if;

               else
                  Error_Msg_N
                    ("selector name should be identifier or OTHERS",
                     Selector_Name);
                  Bad_Aggregate := True;
               end if;

               Next (Selector_Name);
            end loop;

            Next (Assoc);
         end loop;

         if Bad_Aggregate then
            return;
         end if;
      end Step_2;

      --  STEP 3: Find discriminant Values

      Step_3 : declare
         Discrim               : Entity_Id;
         Missing_Discriminants : Boolean := False;

      begin
         if Present (Expressions (N)) then
            Positional_Expr := First (Expressions (N));
         else
            Positional_Expr := Empty;
         end if;

         --  AI05-0115: if the ancestor part is a subtype mark, the ancestor
         --  must not have unknown discriminants.
         --  ??? We are not checking any subtype mark here and this code is not
         --  exercised by any test, so it's likely wrong (in particular
         --  we should not use Root_Type here but the subtype mark, if any),
         --  and possibly not needed.

         if Is_Derived_Type (Typ)
           and then Has_Unknown_Discriminants (Root_Type (Typ))
           and then Nkind (N) /= N_Extension_Aggregate
         then
            Error_Msg_NE
              ("aggregate not available for type& whose ancestor "
               & "has unknown discriminants", N, Typ);
         end if;

         --  Mutably tagged class-wide types do not have discriminants;
         --  however, all class-wide types are considered to have unknown
         --  discriminants.

         if not Is_Mutably_Tagged_Type (Typ)
           and then Has_Unknown_Discriminants (Typ)
           and then Present (Underlying_Record_View (Typ))
         then
            Discrim := First_Discriminant (Underlying_Record_View (Typ));
         elsif Has_Discriminants (Typ) then
            Discrim := First_Discriminant (Typ);
         else
            Discrim := Empty;
         end if;

         --  First find the discriminant values in the positional components

         while Present (Discrim) and then Present (Positional_Expr) loop
            if Discriminant_Present (Discrim) then
               Resolve_Aggr_Expr (Positional_Expr, Discrim);

               --  Ada 2005 (AI-231)

               if Ada_Version >= Ada_2005
                 and then Known_Null (Positional_Expr)
               then
                  Check_Can_Never_Be_Null (Discrim, Positional_Expr);
               end if;

               Next (Positional_Expr);
            end if;

            if Present (Get_Value (Discrim, Component_Associations (N))) then
               Error_Msg_NE
                 ("more than one value supplied for discriminant&",
                  N, Discrim);
            end if;

            Next_Discriminant (Discrim);
         end loop;

         --  Find remaining discriminant values if any among named components

         while Present (Discrim) loop
            Expr := Get_Value (Discrim, Component_Associations (N), True);

            if not Discriminant_Present (Discrim) then
               if Present (Expr) then
                  Error_Msg_NE
                    ("more than one value supplied for discriminant &",
                     N, Discrim);
               end if;

            elsif No (Expr) then
               Error_Msg_NE
                 ("no value supplied for discriminant &", N, Discrim);
               Missing_Discriminants := True;

            else
               Resolve_Aggr_Expr (Expr, Discrim);
            end if;

            Next_Discriminant (Discrim);
         end loop;

         if Missing_Discriminants then
            return;
         end if;

         --  At this point and until the beginning of STEP 6, New_Assoc_List
         --  contains only the discriminants and their values.

      end Step_3;

      --  STEP 4: Set the Etype of the record aggregate

      if Has_Discriminants (Typ)

         --  Handle types with unknown discriminants, excluding mutably tagged
         --  class-wide types because, although they do not have discriminants,
         --  all class-wide types are considered to have unknown discriminants.

        or else (not Is_Mutably_Tagged_Type (Typ)
                  and then Has_Unknown_Discriminants (Typ)
                  and then Present (Underlying_Record_View (Typ)))
      then
         Build_Constrained_Itype (N, Typ, New_Assoc_List);
      else
         Set_Etype (N, Typ);
      end if;

      --  STEP 5: Get remaining components according to discriminant values

      Step_5 : declare
         Dnode           : Node_Id;
         Errors_Found    : Boolean := False;
         Record_Def      : Node_Id;
         Parent_Typ      : Entity_Id;
         Parent_Typ_List : Elist_Id;
         Parent_Elmt     : Elmt_Id;
         Root_Typ        : Entity_Id;

      begin
         if Is_Derived_Type (Typ) and then Is_Tagged_Type (Typ) then
            Parent_Typ_List := New_Elmt_List;

            --  If this is an extension aggregate, the component list must
            --  include all components that are not in the given ancestor type.
            --  Otherwise, the component list must include components of all
            --  ancestors, starting with the root.

            if Nkind (N) = N_Extension_Aggregate then
               Root_Typ := Base_Type (Etype (Ancestor_Part (N)));

            else
               --  AI05-0115: check legality of aggregate for type with a
               --  private ancestor.

               Root_Typ := Root_Type (Typ);
               if Has_Private_Ancestor (Typ) then
                  declare
                     Ancestor      : constant Entity_Id :=
                                       Find_Private_Ancestor (Typ);
                     Ancestor_Unit : constant Entity_Id :=
                                       Cunit_Entity
                                         (Get_Source_Unit (Ancestor));
                     Parent_Unit   : constant Entity_Id :=
                                       Cunit_Entity (Get_Source_Unit
                                         (Base_Type (Etype (Ancestor))));
                  begin
                     --  Check whether we are in a scope that has full view
                     --  over the private ancestor and its parent. This can
                     --  only happen if the derivation takes place in a child
                     --  unit of the unit that declares the parent, and we are
                     --  in the private part or body of that child unit, else
                     --  the aggregate is illegal.

                     if Is_Child_Unit (Ancestor_Unit)
                       and then Scope (Ancestor_Unit) = Parent_Unit
                       and then In_Open_Scopes (Scope (Ancestor))
                       and then
                        (In_Private_Part (Scope (Ancestor))
                          or else In_Package_Body (Scope (Ancestor)))
                     then
                        null;

                     else
                        Error_Msg_NE
                          ("type of aggregate has private ancestor&!",
                           N, Root_Typ);
                        Error_Msg_N ("must use extension aggregate!", N);
                        return;
                     end if;
                  end;
               end if;

               Dnode := Declaration_Node (Base_Type (Root_Typ));

               --  If we don't get a full declaration, then we have some error
               --  which will get signalled later so skip this part. Otherwise
               --  gather components of root that apply to the aggregate type.
               --  We use the base type in case there is an applicable stored
               --  constraint that renames the discriminants of the root.

               if Nkind (Dnode) = N_Full_Type_Declaration then
                  Record_Def := Type_Definition (Dnode);
                  Gather_Components
                    (Base_Type (Typ),
                     Component_List (Record_Def),
                     Governed_By   => New_Assoc_List,
                     Into          => Components,
                     Report_Errors => Errors_Found);

                  if Errors_Found then
                     Error_Msg_N
                       ("discriminant controlling variant part is not static",
                        N);
                     return;
                  end if;
               end if;
            end if;

            Parent_Typ := Base_Type (Typ);
            while Parent_Typ /= Root_Typ loop
               Prepend_Elmt (Parent_Typ, To => Parent_Typ_List);
               Parent_Typ := Etype (Parent_Typ);

               --  Check whether a private parent requires the use of
               --  an extension aggregate.

               if Nkind (Parent (Base_Type (Parent_Typ))) =
                                        N_Private_Type_Declaration
                 or else Nkind (Parent (Base_Type (Parent_Typ))) =
                                        N_Private_Extension_Declaration
               then
                  if Nkind (N) /= N_Extension_Aggregate then
                     Error_Msg_NE
                       ("type of aggregate has private ancestor&!",
                        N, Parent_Typ);
                     Error_Msg_N  ("must use extension aggregate!", N);
                     return;

                  elsif Parent_Typ /= Root_Typ then
                     Error_Msg_NE
                       ("ancestor part of aggregate must be private type&",
                         Ancestor_Part (N), Parent_Typ);
                     return;
                  end if;

               --  The current view of ancestor part may be a private type,
               --  while the context type is always non-private.

               elsif Is_Private_Type (Root_Typ)
                 and then Present (Full_View (Root_Typ))
                 and then Nkind (N) = N_Extension_Aggregate
               then
                  exit when Base_Type (Full_View (Root_Typ)) = Parent_Typ;
               end if;
            end loop;

            --  Now collect components from all other ancestors, beginning
            --  with the current type. If the type has unknown discriminants
            --  use the component list of the Underlying_Record_View, which
            --  needs to be used for the subsequent expansion of the aggregate
            --  into assignments.

            Parent_Elmt := First_Elmt (Parent_Typ_List);
            while Present (Parent_Elmt) loop
               Parent_Typ := Node (Parent_Elmt);

               if Has_Unknown_Discriminants (Parent_Typ)
                 and then Present (Underlying_Record_View (Typ))
               then
                  Parent_Typ := Underlying_Record_View (Parent_Typ);
               end if;

               Record_Def := Type_Definition (Parent (Base_Type (Parent_Typ)));
               Gather_Components (Parent_Typ,
                 Component_List (Record_Extension_Part (Record_Def)),
                 Governed_By   => New_Assoc_List,
                 Into          => Components,
                 Report_Errors => Errors_Found);

               Next_Elmt (Parent_Elmt);
            end loop;

         --  Typ is not a derived tagged type

         else
            Record_Def := Type_Definition (Parent (Base_Type (Typ)));

            if Null_Present (Record_Def) then
               null;

            --  Explicitly add here mutably class-wide types because they do
            --  not have discriminants; however, all class-wide types are
            --  considered to have unknown discriminants.

            elsif not Has_Unknown_Discriminants (Typ)
              or else Is_Mutably_Tagged_Type (Typ)
            then
               Gather_Components
                 (Base_Type (Typ),
                  Component_List (Record_Def),
                  Governed_By   => New_Assoc_List,
                  Into          => Components,
                  Report_Errors => Errors_Found);

            else
               Gather_Components
                 (Base_Type (Underlying_Record_View (Typ)),
                  Component_List (Record_Def),
                  Governed_By   => New_Assoc_List,
                  Into          => Components,
                  Report_Errors => Errors_Found);
            end if;
         end if;

         if Errors_Found then
            return;
         end if;
      end Step_5;

      --  STEP 6: Find component Values

      Component_Elmt := First_Elmt (Components);

      --  First scan the remaining positional associations in the aggregate.
      --  Remember that at this point Positional_Expr contains the current
      --  positional association if any is left after looking for discriminant
      --  values in step 3.

      while Present (Positional_Expr) and then Present (Component_Elmt) loop
         Component := Node (Component_Elmt);
         Resolve_Aggr_Expr (Positional_Expr, Component);

         --  Ada 2005 (AI-231)

         if Ada_Version >= Ada_2005 and then Known_Null (Positional_Expr) then
            Check_Can_Never_Be_Null (Component, Positional_Expr);
         end if;

         if Present (Get_Value (Component, Component_Associations (N))) then
            Error_Msg_NE
              ("more than one value supplied for component &", N, Component);
         end if;

         Next (Positional_Expr);
         Next_Elmt (Component_Elmt);
      end loop;

      if Present (Positional_Expr) then
         Error_Msg_N
           ("too many components for record aggregate", Positional_Expr);
      end if;

      --  Now scan for the named arguments of the aggregate

      while Present (Component_Elmt) loop
         Component := Node (Component_Elmt);
         Expr := Get_Value (Component, Component_Associations (N), True);

         --  Note: The previous call to Get_Value sets the value of the
         --  variable Is_Box_Present.

         --  Ada 2005 (AI-287): Handle components with default initialization.
         --  Note: This feature was originally added to Ada 2005 for limited
         --  but it was finally allowed with any type.

         if Is_Box_Present then
            Check_Box_Component : declare
               Ctyp : constant Entity_Id := Etype (Component);

            begin
               --  Initially assume that the box is for a default-initialized
               --  component and reset to False in cases where that's not true.

               Is_Box_Init_By_Default := True;

               --  If there is a default expression for the aggregate, copy
               --  it into a new association. This copy must modify the scopes
               --  of internal types that may be attached to the expression
               --  (e.g. index subtypes of arrays) because in general the type
               --  declaration and the aggregate appear in different scopes,
               --  and the backend requires the scope of the type to match the
               --  point at which it is elaborated.

               --  If the component has an initialization procedure (IP) we
               --  pass the component to the expander, which will generate
               --  the call to such IP.

               --  If the component has discriminants, their values must
               --  be taken from their subtype. This is indispensable for
               --  constraints that are given by the current instance of an
               --  enclosing type, to allow the expansion of the aggregate to
               --  replace the reference to the current instance by the target
               --  object of the aggregate.

               if Is_Case_Choice_Pattern (N) then

                  --  Do not transform box component values in a case-choice
                  --  aggregate.

                  Add_Association
                   (Component      => Component,
                    Expr           => Empty,
                    Assoc_List     => New_Assoc_List,
                    Is_Box_Present => True);

               elsif Present (Parent (Component))
                 and then Nkind (Parent (Component)) = N_Component_Declaration
                 and then Present (Expression (Parent (Component)))
               then
                  --  If component declaration has an initialization expression
                  --  then this is not a case of default initialization.

                  Is_Box_Init_By_Default := False;

                  Expr :=
                    New_Copy_Tree_And_Copy_Dimensions
                      (Expression (Parent (Component)),
                       New_Scope => Current_Scope,
                       New_Sloc  => Sloc (N));

                  --  As the type of the copied default expression may refer
                  --  to discriminants of the record type declaration, these
                  --  non-stored discriminants need to be rewritten into stored
                  --  discriminant values for the aggregate. This is required
                  --  in GNATprove mode, and is adopted in all modes to avoid
                  --  special-casing GNATprove mode.

                  if Is_Array_Type (Etype (Expr)) then
                     declare
                        Rec_Typ : constant Entity_Id := Scope (Component);
                        --  Root record type whose discriminants may be used as
                        --  bounds in range nodes.

                        Assoc  : Node_Id;
                        Choice : Node_Id;
                        Index  : Node_Id;

                     begin
                        --  Rewrite the range nodes occurring in the indexes
                        --  and their types.

                        Index := First_Index (Etype (Expr));
                        while Present (Index) loop
                           Rewrite_Range (Rec_Typ, Index);
                           Rewrite_Range
                             (Rec_Typ, Scalar_Range (Etype (Index)));

                           Next_Index (Index);
                        end loop;

                        --  Rewrite the range nodes occurring as aggregate
                        --  bounds and component associations.

                        if Nkind (Expr) = N_Aggregate then
                           if Present (Aggregate_Bounds (Expr)) then
                              Rewrite_Range (Rec_Typ, Aggregate_Bounds (Expr));
                           end if;

                           if Present (Component_Associations (Expr)) then
                              Assoc := First (Component_Associations (Expr));
                              while Present (Assoc) loop
                                 Choice := First (Choices (Assoc));
                                 while Present (Choice) loop
                                    Rewrite_Range (Rec_Typ, Choice);

                                    Next (Choice);
                                 end loop;

                                 Next (Assoc);
                              end loop;
                           end if;
                        end if;
                     end;
                  end if;

                  Add_Association
                    (Component  => Component,
                     Expr       => Expr,
                     Assoc_List => New_Assoc_List);
                  Set_Has_Self_Reference (N);

               elsif Needs_Simple_Initialization (Ctyp)

                  --  Mutably tagged class-wide type components are initialized
                  --  by the expander calling their IP subprogram.

                 or else Is_Mutably_Tagged_CW_Equivalent_Type (Ctyp)
                 or else Has_Non_Null_Base_Init_Proc (Ctyp)
                 or else not Expander_Active
               then
                  Add_Association
                    (Component      => Component,
                     Expr           => Empty,
                     Assoc_List     => New_Assoc_List,
                     Is_Box_Present => True);

               --  Otherwise we only need to resolve the expression if the
               --  component has partially initialized values (required to
               --  expand the corresponding assignments and run-time checks).

               elsif Present (Expr)
                 and then Is_Partially_Initialized_Type (Ctyp)
               then
                  Resolve_Aggr_Expr (Expr, Component);
               end if;
            end Check_Box_Component;

         elsif No (Expr) then

            --  Ignore hidden components associated with the position of the
            --  interface tags: these are initialized dynamically.

            if No (Related_Type (Component)) then
               Error_Msg_NE
                 ("no value supplied for component &!", N, Component);
            end if;

         else
            Resolve_Aggr_Expr (Expr, Component);
         end if;

         Next_Elmt (Component_Elmt);
      end loop;

      --  STEP 7: check for invalid components + check type in choice list

      Step_7 : declare
         Assoc     : Node_Id;
         New_Assoc : Node_Id;

         Selectr : Node_Id;
         --  Selector name

         Typech : Entity_Id;
         --  Type of first component in choice list

      begin
         if Present (Component_Associations (N)) then
            Assoc := First (Component_Associations (N));
         else
            Assoc := Empty;
         end if;

         Verification : while Present (Assoc) loop
            Selectr := First (Choices (Assoc));
            Typech := Empty;

            if Nkind (Selectr) = N_Others_Choice then

               --  Ada 2005 (AI-287): others choice may have expression or box

               if No (Others_Etype) and then Others_Box = 0 then
                  Error_Msg_N
                    ("OTHERS must represent at least one component", Selectr);

               elsif Others_Box = 1 and then Warn_On_Redundant_Constructs then
                  Error_Msg_N ("OTHERS choice is redundant?r?", Box_Node);
                  Error_Msg_N
                    ("\previous choices cover all components?r?", Box_Node);
               end if;

               exit Verification;
            end if;

            while Present (Selectr) loop
               Component := Empty;
               New_Assoc := First (New_Assoc_List);
               while Present (New_Assoc) loop
                  Component := First (Choices (New_Assoc));

                  if Chars (Selectr) = Chars (Component) then
                     if Style_Check then
                        Check_Identifier (Selectr, Entity (Component));
                     end if;

                     exit;
                  end if;

                  Next (New_Assoc);
               end loop;

               --  If we found an association, then this is a legal component
               --  of the type in question.

               pragma Assert (if Present (New_Assoc) then Present (Component));

               --  If no association, this is not a legal component of the type
               --  in question, unless its association is provided with a box.

               if No (New_Assoc) then
                  if Box_Present (Parent (Selectr)) then

                     --  This may still be a bogus component with a box. Scan
                     --  list of components to verify that a component with
                     --  that name exists.

                     declare
                        C : Entity_Id;

                     begin
                        C := First_Component (Typ);
                        while Present (C) loop
                           if Chars (C) = Chars (Selectr) then

                              --  If the context is an extension aggregate,
                              --  the component must not be inherited from
                              --  the ancestor part of the aggregate.

                              if Nkind (N) /= N_Extension_Aggregate
                                or else
                                  Scope (Original_Record_Component (C)) /=
                                    Etype (Ancestor_Part (N))
                              then
                                 exit;
                              end if;
                           end if;

                           Next_Component (C);
                        end loop;

                        if No (C) then
                           Error_Msg_Node_2 := Typ;
                           Error_Msg_N ("& is not a component of}", Selectr);
                        end if;
                     end;

                  elsif Chars (Selectr) /= Name_uTag
                    and then Chars (Selectr) /= Name_uParent
                  then
                     if not Has_Discriminants (Typ) then
                        Error_Msg_Node_2 := Typ;
                        Error_Msg_N ("& is not a component of}", Selectr);
                     else
                        Error_Msg_N
                          ("& is not a component of the aggregate subtype",
                            Selectr);
                     end if;

                     Check_Misspelled_Component (Components, Selectr);
                  end if;

               elsif No (Typech) then
                  Typech := Base_Type (Etype (Component));

               --  AI05-0199: In Ada 2012, several components of anonymous
               --  access types can appear in a choice list, as long as the
               --  designated types match.

               elsif Typech /= Base_Type (Etype (Component)) then
                  if Ada_Version >= Ada_2012
                    and then Ekind (Typech) = E_Anonymous_Access_Type
                    and then
                       Ekind (Etype (Component)) = E_Anonymous_Access_Type
                    and then Base_Type (Designated_Type (Typech)) =
                             Base_Type (Designated_Type (Etype (Component)))
                    and then
                      Subtypes_Statically_Match (Typech, (Etype (Component)))
                  then
                     null;

                  elsif not Box_Present (Parent (Selectr)) then
                     Error_Msg_N
                       ("components in choice list must have same type",
                        Selectr);
                  end if;
               end if;

               Next (Selectr);
            end loop;

            Next (Assoc);
         end loop Verification;
      end Step_7;

      --  STEP 8: replace the original aggregate

      Step_8 : declare
         New_Aggregate : constant Node_Id := New_Copy (N);

      begin
         Set_Expressions            (New_Aggregate, No_List);
         Set_Etype                  (New_Aggregate, Etype (N));
         Set_Component_Associations (New_Aggregate, New_Assoc_List);
         Set_Check_Actuals          (New_Aggregate, Check_Actuals (N));

         Rewrite (N, New_Aggregate);
      end Step_8;

      --  Check the dimensions of the components in the record aggregate

      Analyze_Dimension_Extension_Or_Record_Aggregate (N);

      --  Do a pass for constructors which rely on things being fully expanded

      declare
         function Resolve_Make_Expr (N : Node_Id) return Traverse_Result;
         --  Recurse in the aggregate and resolve references to 'Make

         function Resolve_Make_Expr (N : Node_Id) return Traverse_Result is
         begin
            if Nkind (N) = N_Attribute_Reference
              and then Attribute_Name (N) = Name_Make
            then
               Set_Analyzed (N, False);
               Resolve (N);
            end if;

            return OK;
         end Resolve_Make_Expr;

         procedure Search_And_Resolve_Make_Expr is new
           Traverse_Proc (Resolve_Make_Expr);
      begin
         Search_And_Resolve_Make_Expr (N);
      end;
   end Resolve_Record_Aggregate;

   -----------------------------
   -- Check_Can_Never_Be_Null --
   -----------------------------

   procedure Check_Can_Never_Be_Null (Typ : Entity_Id; Expr : Node_Id) is
      Comp_Typ : Entity_Id;

   begin
      pragma Assert
        (Ada_Version >= Ada_2005
          and then Present (Expr)
          and then Known_Null (Expr));

      case Ekind (Typ) is
         when E_Array_Type  =>
            Comp_Typ := Component_Type (Typ);

         when E_Component
            | E_Discriminant
         =>
            Comp_Typ := Etype (Typ);

         when others =>
            return;
      end case;

      if Can_Never_Be_Null (Comp_Typ) then

         --  Here we know we have a constraint error. Note that we do not use
         --  Apply_Compile_Time_Constraint_Error here to the Expr, which might
         --  seem the more natural approach. That's because in some cases the
         --  components are rewritten, and the replacement would be missed.
         --  We do not mark the whole aggregate as raising a constraint error,
         --  because the association may be a null array range.

         Error_Msg_N
           ("(Ada 2005) NULL not allowed in null-excluding component??", Expr);
         Error_Msg_N
           ("\Constraint_Error will be raised at run time??", Expr);

         Rewrite (Expr,
           Make_Raise_Constraint_Error
             (Sloc (Expr), Reason => CE_Access_Check_Failed));
         Set_Etype    (Expr, Comp_Typ);
         Set_Analyzed (Expr);
      end if;
   end Check_Can_Never_Be_Null;

   ---------------------
   -- Sort_Case_Table --
   ---------------------

   procedure Sort_Case_Table (Case_Table : in out Case_Table_Type) is
      U : constant Int := Case_Table'Last;
      K : Int;
      J : Int;
      T : Case_Bounds;

   begin
      K := 1;
      while K < U loop
         T := Case_Table (K + 1);

         J := K + 1;
         while J > 1
           and then Expr_Value (Case_Table (J - 1).Lo) > Expr_Value (T.Lo)
         loop
            Case_Table (J) := Case_Table (J - 1);
            J := J - 1;
         end loop;

         Case_Table (J) := T;
         K := K + 1;
      end loop;
   end Sort_Case_Table;

end Sem_Aggr;
