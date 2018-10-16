declare Counter MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment
   Statement = {NewCell nil}
   Environment = {NewCell nil}
   SemanticStack = {NewCell nil}
   Counter = {NewCell 0}
   SemanticStatement = statement(st:Statement env:Environment)

%Stack Functions
fun {Pop S} case @S of nil then nil [] X|X1 then S:=X1 X end end
proc {Push S E} S:=E|@S end
fun {IsEmpty S} @S==nil end
%Nop
proc {Nop}
   {Main}
end

fun {GetNewVar}
   Counter:=@Counter+1
   sas(@Counter)
end

fun {CopyEnv L N}
   %{Browse N#L}
   case L of
      nil then N|nil
   [] X|Xr then if X.1==N.1 then {CopyEnv Xr N} else X|{CopyEnv Xr N} end
   end
end


fun {AdjEnv L X}
   %{Browse x#L}
   case X of
      ident(Y) then {CopyEnv L [Y {GetNewVar}]}
   end
end

proc {Var}
   local T in
      T = {Pop SemanticStack}
    %  {Browse T.st.1#T.st.2.1}
      case T.st of
	 nil then {Main}
      [] X|Xr then {Push SemanticStack statement(st:Xr env:{AdjEnv T.env X})} {Main}
      end
   end
end

   proc {MainUtil S E}
	 case S of
	 nil then {Main}
	 [] nop then {Browse nopMatched#E} {Nop}
	 [] var then {Browse var} {Var}
	 [] record then {Browse record}
	 [] bind then {Browse bind}
	 [] conditional then {Browse conditional}
	 [] match then {Browse match}
	 [] apply then {Browse apply}
	 [] Y|Yr then {Push SemanticStack statement(st:Yr env:E)} {Push SemanticStack statement(st:Y env:E)} {Main}
	 end
   end
 
   proc {Main}
      local T in
	 T = {Pop SemanticStack}
	 case T of
	    nil then skip
	    [] statement(st:X env:E) then {Browse E} {MainUtil X E}
	 end
      end
   end
   
   {Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(x) [nop]]]] env:nil)}
   {Main}