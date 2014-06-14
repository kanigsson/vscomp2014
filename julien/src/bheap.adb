with Ada.Containers; use Ada.Containers;

package body BHeap with SPARK_Mode is

   function Make_Empty_Node return Binomial_Heap_Node is
      (Key => Empty_Node, Degree => 0, others => Empty_Node);

   function Find_Min_Node (Arg : Node_Key) return Node_Key is
      X, Y : Node_Key := Arg;
      Min : Node_Key := Arg;
   begin
      while X /= Empty_Node loop
         if X < Min then
            Y := X;
            min := X;
         end if;
         X := Node_Sets.Element (Nodes, X).Sibling;
      end loop;

      return Y;
   end Find_Min_Node;

   function Reverse_Node (Node : Node_Key; Sibl : Node_Key) return Node_Key is
      Actual_Node : Binomial_Heap_Node := Node_Sets.Element (Nodes, Node);
      Ret : Node_Key;
   begin
      if Actual_Node.Sibling /= Empty_Node then
         Ret := Reverse_Node (Actual_Node.Sibling, Node);
      else
         Ret := Node;
      end if;

      Actual_Node.Sibling := Sibl;
      Node_Sets.Replace_Element (Nodes, Node, Actual_Node);

      return Ret;
   end Reverse_Node;

   procedure Merge_Nodes (Heap : in out Binomial_Heap; Bin_Heap : Node_Key) is
      Temp1 : Node_Key := Heap.Root;
      Temp2 : Node_Key := Bin_Heap;
   begin

      while Temp1 /= Empty_Node and then Temp2 /= Empty_Node loop
         declare
            Temp1_Node : Binomial_Heap_Node := Node_Sets.Element (Nodes, Temp1);
            Temp2_Node : Binomial_Heap_Node := Node_Sets.Element (Nodes, Temp2);
            Tmp : Node_Key;
         begin
            if Temp1_Node.Degree = Temp2_Node.Degree then
               Tmp := Temp2;
               Temp2 := Temp2_Node.Sibling;
               Temp2_Node.Sibling := Temp1_Node.Sibling;
               Temp1_Node.Sibling := Tmp;
               Node_Sets.Replace_Element (Nodes, Temp1, Temp1_node);
               Node_Sets.Replace_Element (Nodes, Tmp, Temp2_Node);
               Temp1 := Temp2_Node.Sibling;
            elsif Temp1_Node.Degree < Temp2_Node.Degree then
               if Temp1_Node.Sibling = Empty_Node
                 or else Node_Sets.Element
                   (Nodes, Temp1_Node.Sibling).Degree > Temp2_Node.Degree
               then
                  Tmp := Temp2;
                  Temp2 := Temp2_Node.Sibling;
                  Temp2_Node.Sibling := Temp1_Node.Sibling;
                  Temp1_Node.Sibling := Tmp;
                  Node_Sets.Replace_Element (Nodes, Temp1, Temp1_node);
                  Node_Sets.Replace_Element (Nodes, Tmp, Temp2_Node);
                  Temp1 := Temp2_Node.Sibling;
               else
                  Temp1 := Temp1_Node.Sibling;
               end if;
            else
               Tmp := Temp1;
               Temp1 := Temp2;
               Temp2 := Temp2_Node.Sibling;
               Temp2_Node.Sibling := Tmp;
               Node_Sets.Replace_Element (Nodes, Temp1, Temp2_Node);
               if Tmp = Heap.Root then
                  Heap.Root := Temp1;
               end if;
            end if;
         end;
      end loop;

      if Temp1 = Empty_Node then
         Temp1 := Heap.Root;
         declare
            Temp1_Node : Binomial_Heap_Node := Node_Sets.Element (Nodes, Temp1);
         begin
            while Temp1_Node.Sibling /= Empty_Node loop
               Temp1 := Temp1_Node.Sibling;
               Temp1_Node := Node_Sets.Element (Nodes, Temp1);
            end loop;
            Temp1_Node.Sibling := Temp2;
            Node_Sets.Replace_Element (Nodes, Temp1, Temp1_Node);
         end;
      end if;
   end Merge_Nodes;

   procedure Union_Nodes (Heap : in out Binomial_Heap; Bin_Heap : Node_Key) is
      Temp : Node_Key := Empty_Node;
      Prev_Temp : Node_Key := Heap.Root;
      Next_Temp : Node_Key := Node_Sets.Element (Nodes, Heap.Root).Sibling;
   begin
      Merge_Nodes (Heap, Bin_Heap);

      while Next_Temp /= Empty_Node loop
         declare
            Next_Node : Binomial_Heap_Node :=
              Node_Sets.Element (Nodes, Next_Temp);
            Temp_Node : Binomial_Heap_Node :=
              Node_Sets.Element (Nodes, Temp);
         begin
            if Temp_Node.Degree /= Next_Node.Degree
              or else (Next_Node.Sibling /= Empty_Node
                       and then Node_Sets.Element
                         (Nodes, Next_Node.Sibling).Degree = Temp_Node.Degree)
            then
               Prev_Temp := Temp;
               Temp := Next_Temp;
            elsif Temp <= Next_Temp then
               Temp_Node.Sibling := Next_Node.Sibling;
               Next_Node.Parent := Temp;
               Next_Node.Sibling := Temp_Node.Child;
               Temp_Node.Child := Next_Temp;
               Temp_Node.Degree := Temp_Node.Degree + 1;
               Node_Sets.Replace_Element (Nodes, Temp, Temp_Node);
               Node_Sets.Replace_Element (Nodes, Next_Temp, Next_Node);
            else
               if Prev_Temp = Empty_Node then
                  Heap.Root := Next_Temp;
               else
                  declare
                     Prev_Node : Binomial_Heap_Node := Node_Sets.Element
                       (Nodes, Prev_Temp);
                  begin
                     Prev_Node.Sibling := Next_Temp;
                     Node_Sets.Replace_Element (Nodes, Prev_Temp, Prev_Node);
                  end;
               end if;
               Temp_Node.Parent := Next_Temp;
               Temp_Node.Sibling := Next_Node.Child;
               Next_Node.Child := Temp;
               Next_Node.Degree := Next_Node.Degree + 1;
               Temp := Next_Temp;
               Node_Sets.Replace_Element (Nodes, Temp, Temp_Node);
               Node_Sets.Replace_Element (Nodes, Next_Temp, Next_Node);
            end if;
         end;
         Next_Temp := Node_Sets.Element (Nodes, Temp).Sibling;
      end loop;
   end Union_Nodes;

   procedure Extract_Min (Heap : in out Binomial_Heap; Min : out Binomial_Heap_Node) is
      Temp : Node_Key := Heap.Root;
      Prev_Temp : Node_Key := Empty_Node;
      Min_Node : Node_Key;
      Fake_Node : Node_Key;
   begin
      if Heap.Size = 0 then
         Min := Make_Empty_Node;
         return;
      end if;

      Min_Node := Find_Min_Node (Heap.Root);
      while Temp /= Min_Node loop
         Prev_Temp := Temp;
         Temp := Node_Sets.Element (Nodes, Temp).Sibling;
      end loop;

      if Prev_Temp = Empty_Node then
         Heap.Root := Node_Sets.Element (Nodes, Temp).Sibling;
      else
         declare
            Prev_Node : Binomial_Heap_Node := Node_Sets.Element (Nodes, Prev_Temp);
         begin
            Prev_Node.Sibling := Node_Sets.Element (Nodes, Temp).Sibling;
            Node_Sets.Replace_Element (Nodes, Prev_Temp, Prev_Node);
         end;
      end if;
      Temp := Node_Sets.Element (Nodes, Temp).Child;
      Fake_Node := Temp;

      declare
         Temp_Node : Binomial_Heap_Node;
      begin
         while Temp /= Empty_Node loop
            Temp_Node := Node_Sets.Element (Nodes, Temp);
            Temp_Node.Parent := Empty_Node;
            Node_Sets.Replace_Element (Nodes, Temp, Temp_Node);
            Temp := Temp_Node.Sibling;
         end loop;
      end;

      if Heap.Root = Empty_Node and then Fake_Node = Empty_Node then
         Heap.Size := 0;
      elsif Heap.Root = Empty_Node and then Fake_Node /= Empty_Node then
         Heap.Root := Reverse_Node (Fake_Node, Empty_Node);
         Heap.Size := Heap.Size - 1;
      elsif Heap.Root /= Empty_Node and then Fake_Node = Empty_Node then
         Heap.Size := Heap.Size - 1;
      else
         -- Never reached, might be the failure
         Union_Nodes (Heap, Reverse_Node (Fake_Node, Empty_Node));
         Heap.Size := Heap.Size - 1;
      end if;
   end Extract_Min;

end BHeap;
