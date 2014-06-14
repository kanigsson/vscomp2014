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

   procedure Extract_Min (Heap : Binomial_Heap; Min : out Binomial_Heap_Node) is
   begin
      if Heap.Size = 0 then
         Min := Make_Empty_Node;
         return;
      end if;
      Min := Node_Sets.Element (Nodes, Heap.Root);

   end Extract_Min;

end BHeap;
