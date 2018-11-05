\insert 'Unify.oz'
\insert 'SingleAssignmentStore.oz'
\insert 'Util.oz'

declare Counter MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment Match Conditional
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
    
    %This function keeps track of the new variables introduced in SAS. It also ensures that everytime 
    % a unique variable is introduced
    fun {GetNewVar}
       Counter:=@Counter+1
       {AddKeyToSAS @Counter}
       @Counter
    end

    %Returns the copy of the environment with variable N. It takes care of repitions and makes sure to replave them
    % Don't directlt call this function for new identifiers
    fun {CopyEnv L N}
       %{Browse N#L}
       case L of
          nil then N|nil
       [] X|Xr then if X.1==N.1 then {CopyEnv Xr N} else X|{CopyEnv Xr N} end
       end
    end

    % Performs the adj operation on environment. X is the new identifier of the form ident(Z)
    fun {AdjEnv L X}
       %{Browse x#L}
       case X of
          ident(Y) then {CopyEnv L [ident(Y) {GetNewVar}]}
       end
    end

    % Procedure to handle the var command.
    % T = statement(st:[ident(newVariable) <Rest of the statement>] env:E)
    proc {Var T}
        %  {Browse T.st.1#T.st.2.1}
        case T.st of
          nil then {Main}
          [] X|Xr then {Push SemanticStack statement(st:Xr env:{AdjEnv T.env X})} {Main}
        end
    end

    % Procedure to handle the bind command.
    proc {Bind T}
       local X Y in
          X = {FindX T.env T.st.1}
          Y = {FindX T.env T.st.2.1}
          {Browse T.env#X#Y}
          %{Browse {Dictionary.keys SAS}}
          %{Browse {Dictionary.items SAS}}
          %{Browse {RetrieveFromSAS 1}}
          {Browse 'In Bind, before unify'}
          %{BindRefToKeyInSAS X Y}
          {Unify T.st.1 T.st.2.1 T.env}
          {Main}
          %{Browse X}
       end
    end

    % T is of the form statement(st:[ident(X) s1 s2] env:E)
    proc {Conditonal T}
      local S in
        S = {RetrieveFromSAS {FindX T.env T.st.1}}
        case S
        of equivalence(X) then {Exception.'raise' variableUnbound(conditional)}
        [] t then {Push SemanticStack statement(st:T.st.2.1 env:T.env)}
        [] f then {Push SemanticStack statement(st:T.st.2.2.1 env:T.env)}
        end 
      end
    end

    fun {AddEnvPattern Xs P E}
        case Xs
        of nil then E
        [] X|Xr then {AddEnvPattern Xr P {CopyEnv E [{GetIdentRecord P X.1} {FindX E X.2}]}}
        end
    end

%    proc {Match T}
%      local S P in
%        S = {RetrieveFromSAS {FindX T.env T.st.1}}
%        P = T.st.2.1
%        case S
%        of equivalence(X) then {Exception.'raise' variableUnbound(match)}
%        [] value (X) then
%          case X.2.1#P.2.1
%          of (literal(Y))#(literal(Z)) then 
%	     if (Y==Z andthen ({Len X.2.2}=={Len P.2.2}) andthen {L1SubsetL2 P.2.2 X.2.2}) 
%              then {Push SemanticStack statement(st:T.st.2.2.1 env:{AddEnvPattern X.2.2 P.2.2 T.env})} 
%              else {Push SemanticStack statement(st:T.st.2.2.2.1 env:T.env)} 
%            end
%	  end
%	end
%      end
%    end

    % S = Stack and E = Environment
    proc {MainUtil S E}
	  case S.1 of
          nil then {Main}
          [] nop then {Browse nopMatched#E} {Nop}
          [] var then {Browse var} {Var statement(st:S.2 env:E)}
          [] record then {Browse record}
          [] bind then {Browse bind} {Bind statement(st:S.2 env:E)}
          [] conditional then {Browse conditional} {Conditonal statement(st:S.2 env:E)}
          [] match then {Browse match} {Match statement(st:S.2 env:E)}
          [] apply then {Browse apply}
          [] Y|Yr then {Push SemanticStack statement(st:S.2 env:E)} {Push SemanticStack statement(st:S.1 env:E)} {Main}
          end
    end
 
    proc {Main}
      local T in
          T = {Pop SemanticStack}
          case T of
            nil then skip
            [] statement(st:X env:E) then {Browse E} if X==nil then {Main} else {MainUtil X E} end
          end
      end
    end
   
   %{Push SemanticStack statement(st:[[var ident(x) [var ident(y) [var ident(x) [nop]]]][var ident(x) [nop]]] env:nil)}
    {Push SemanticStack statement(st:[var ident(x) [bind ident(x) literal(1)][conditional ident(x) [var
											   idet(y) [nop]] [var ident(z) [nop]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(z)] [bind ident(z) ident(y)] [bind ident(x) ident(y)]]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) [record literal(a) [[literal(1) ident(y)] [literal(2) literal(10)]]]] [bind ident(x) [record literal(a) [[literal(1) literal(69)] [literal(2) ident(z)]]]]]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) [record literal(a) [[literal(1) literal(5)] [literal(2) ident(z)]]]] [bind ident(y) [record literal(a) [[literal(1) ident(z)] [literal(2) literal(10)]]]] [bind ident(x) ident(y)]]]]] env:nil)}
   %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [[bind ident(x) [record literal(p) [[literal(n) ident(y)]]]] [bind ident(y) [record literal(p) [[literal(n) ident(x)]]]] [bind ident(x) ident(y)] ]]] env:nil)}
   %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [[bind ident(x) [record literal(p) [[literal(n) ident(y)]]]] [bind ident(y) literal(69)]]]] env:nil)}
    {Main}
    {Browse {Dictionary.items SAS}}
    {Browse 'Hello123'}
    {Browse 'Hello123'}
    %{Browse {Dictionary.condGet 
