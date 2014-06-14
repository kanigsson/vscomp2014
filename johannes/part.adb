package body Part is

   function Mem (X : Set; Elt : Integer) return Boolean is
     (for some I in X'Range => Elt = X (I));

   procedure Swap (X : in out Set; A, B : Valid_Range)
     with Post =>
       (X (A) = X'Old (B) and then X (B) = X'Old (A) and then
          (for all I in X'Range =>
                 (if I /= A and then I /= B then X (I) = X'Old (I))));

   procedure Split_Partition (A : in out Subset;
                              X : Set;
                              Result : in out Partition;
                              Part_Count : in out Range_And_Zero);

   ----------
   -- Swap --
   ----------

   procedure Swap (X : in out Set; A, B : Valid_Range) is
      Tmp : Integer := X (A);
   begin
      X (A) := X (B);
      X (B) := Tmp;
   end Swap;


   procedure Split_Partition (A : in out Subset;
                              X : Set;
                              Result : in out Partition;
                              Part_Count : in out Range_And_Zero) is
      First : Valid_Range := A'First;
      Last  : Valid_Range := A'Last;
   begin
      First := A'First;
      Last := A'Last;
      while First <= Last loop
         if Mem (X, A (First)) then
            First := First + 1;
         else
            Swap (A, First, Last);
            Last := Last - 1;
         end if;
      end loop;
      Part_Count := Part_Count + 1;
      Result (Part_Count) := A'First;
      if First = A'First or else Last = A'Last then
         null;
      else
         Part_Count := Part_Count + 1;
         Result (Part_Count) := First;
      end if;
   end Split_Partition;

   ------------
   -- Refine --
   ------------

   function Refine (A : in out Set; P : Partition; X : Set) return Partition is
      Last_Index : Valid_Range := 1;
      Result     : Partition;
      Cur_Part_Cnt : Range_And_Zero := 1;
   begin
      for PI in P'Range loop
         --  we have in fact found all partitions already
         if P (PI) = 0 then
            exit;
         end if;

         --  we now act split the current partition

         Split_Partition (A (Last_Index .. P (PI) - 1),
                          X,
                          Result,
                          Cur_Part_Cnt);

      end loop;
      return Result;
   end Refine;

end Part;
