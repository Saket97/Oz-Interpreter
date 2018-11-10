\insert 'Unify.oz'
%\insert 'SingleAssignmentStore.oz'
\insert 'Util.oz'

declare Counter MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment Match Conditional GetEnv File
    Statement = {NewCell nil}
    Environment = {NewCell nil}
    SemanticStack = {NewCell nil}
    Counter = {NewCell 0}
SemanticStatement = statement(st:Statement env:Environment)
    %File = {New Open.file init(name: 'test.txt' flags:[write create] mode:mode(owner:[read write] group:[read write]))}

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
    % Don't directly call this function for new identifiers
    fun {CopyEnv L N}
       %{Show N#L}
       case L of
          nil then N|nil
       [] X|Xr then if X.1==N.1 then {CopyEnv Xr N} else X|{CopyEnv Xr N} end
       end
    end

    % Performs the adj operation on environment. X is the new identifier of the form ident(Z)
    fun {AdjEnv L X}
       %{Show x#L}
       case X of
          ident(Y) then {CopyEnv L [ident(Y) {GetNewVar}]}
       end
    end

    % Procedure to handle the var command.
    % T = statement(st:[ident(newVariable) <Rest of the statement>] env:E)
    proc {Var T}
        %  {Show T.st.1#T.st.2.1}
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
          %{Show T.env#X#T.st.2.1}
          %{Show {Dictionary.keys SAS}}
          %{Show {Dictionary.items SAS}}
          %{Show {RetrieveFromSAS 1}}
          %{Show 'In Bind, before unify'}
          local Q in
             case T.st.2.1
             of Z|Zr then if Z==proc1 then Q=T.st.2.1#{ProcRet T.st.2.1 T.env} else Q=T.st.2.1 end
             else
                Q=T.st.2.1
             end
          %{BindRefToKeyInSAS X Y}
             %{Show T.st.1#Q#T.env#'Hi yes'}
             {Unify T.st.1 Q T.env}
             {Main}
          end
          %{Show X}
       end
    end

    % T is of the form statement(st:[ident(X) s1 s2] env:E)
    proc {Conditonal T}
      local S in
        S = {RetrieveFromSAS {FindX T.env T.st.1}}
        case S
        of equivalence(X) then {Exception.'raise' variableUnbound(conditional)}
        [] t then {Push SemanticStack statement(st:T.st.2.1 env:T.env)} {Main}
        [] f then {Push SemanticStack statement(st:T.st.2.2.1 env:T.env)} {Main}
        end 
      end
    end

    fun {Find V T1 T2}
       case T1#T2
       of nil#nil then notFound
       [](X|Xr)#(Y|Yr) then if Y==value(V) then X else {Find V Xr Yr} end
       end
    end

    fun {GetSASVarFromVal V}
       local T1 T2 in
	  T1 = {Dictionary.keys SAS}
	  T2 = {Dictionary.items SAS}
	  {Find V T1 T2}
       end
    end
 
    fun {AddEnvPattern Xs P E}
        case Xs
        of nil then E
	[] X|Xr then
	   case X.2.1
	   of ident(Z) then {AddEnvPattern Xr P {CopyEnv E [{GetIdentRecord P X.1} {FindX E X.2.1}]}}
	   [] equivalence(Z) then {AddEnvPattern Xr P {CopyEnv E [{GetIdentRecord P X.1} Z]}}
	   else
	      local T T2 in
		 T2 = {GetSASVarFromVal X.2.1}
		 if T2 == notFound
		 then T = {AdjEnv E {GetIdentRecord P X.1}} {Unify {GetIdentRecord P X.1} X.2.1 T}  {AddEnvPattern Xr P T}
		 else T = {CopyEnv E [{GetIdentRecord P X.1} T2]}  {AddEnvPattern Xr P T}
		 end
	      end
	   end
        end
    end

    % T is of the form statement(st:[ident(X) s1 s2] env:E)
    proc {Match T}
      local S P in
         S = {RetrieveFromSAS {FindX T.env T.st.1}}
	 P = T.st.2.1
	 {Show T.st.1}
	 {Show s#S#p#P}
	 case S
	 of equivalence(X) then {Exception.'raise' variableUnbound(match)}
	 [] X then case X.2.1#P.2.1
			  of (literal(Y))#(literal(Z)) then {Show yipee1} {Show y#Y#z#Z} {Show X.2.2.1#P.2.2.1}{Show {L1SubsetL2 P.2.2.1 X.2.2.1}}
			     if (Y==Z andthen {Len X.2.2.1} == {Len P.2.2.1}) andthen {L1SubsetL2 P.2.2.1 X.2.2.1}
			     then {Push SemanticStack statement(st:T.st.2.2.1 env:{AddEnvPattern X.2.2.1 P.2.2.1 T.env})}{Main}
			     else {Push SemanticStack statement(st:T.st.2.2.2.1 env:T.env)} {Main}
			     end
			  end
	 end
      end
    end

%    proc {GetClosure S E Local}
%       case S
%       of X|Xr then
%	  case X
%	  of ident(Z) then if {ListExistClosure Local X} then {GetClosure Xr E Local} else [X {FindX E X}]|{GetClosure Xr E Local} end
%	  [] Y|Yr then local T1 T2 in
%			  T1={GetClosure Y E Local}
%			  T2={GetClosure Yr E Local}
%			  {Merge T1 {Merge T2 {GetClosure Xr E Local}}}
%		       end
%	  else {GetClosure Xr E Local}   
%	  end
%       [] nil then nil
%       else {GetClosure Xr E Local}	  
%       end
%    end

    fun {GetClosure S E Local}
       case S
       of ident(Z) then if {ListExistClosure Local S} then nil else [S {FindX E S}]|nil end
       [] X|Xr then {Merge {GetClosure X E Local} {GetClosure Xr E Local}}
       else nil
       end
    end

    fun {ProcRet S E}
       {GetClosure S.2.2.1 E S.2.1}
    end

    proc {Proc S E}
       local CloEnv in
          CloEnv = {GetClosure S.2.2.1 E S.2.1}
          %{Show cloEnv#CloEnv}
          %{Show value([S CloEnv])}
       end
    end

    % Note does not work for literals i.e. the arguments of the procedure has to be an identifier.It can't be a value
    fun {GenEnv L1 L2 E}
       %{Show 'Hi'}
       %{Show L1#L2}
       case L1#L2
       of nil#nil then nil
       [] (X|Xr)#(Y|Yr) then [X {FindX E Y}]|{GenEnv Xr Yr E}
       end
    end

    proc {Apply T}
       local X E in
          X = {RetrieveFromSAS {FindX T.env T.st.1}}
          {Show T}
          case X
          of (proc1|PVal)#Closure then E={Merge {Merge {GenEnv PVal.1 T.st.2 T.env} Closure} [T.st.1 X] }
          end
          {Show 'In Proc'}
          case X
          of V#C then {Push SemanticStack statement(st:V.2.2.1 env:E)}
          end
          %{Show E}
          {Main}
       end
    end

    % X,Y,Z are of the form ident(x) and E is the environment
    proc {Add X Y Z E}
       local T1 T2 in
	  T1 = {RetrieveFromSAS {FindX E X}}
	  T2 = {RetrieveFromSAS {FindX E Y}}
       case T1#T2
       of (literal(N1))#(literal(N2)) then {Push SemanticStack statement(st:[bind Z literal(N1+N2)] env: E)} {Main}
       else
	  {Exception.'raise' variableUnbound(add)}
       end
       end
    end

    proc {Product X Y Z E}
       local T1 T2 in
	  T1 = {RetrieveFromSAS {FindX E X}}
	  T2 = {RetrieveFromSAS {FindX E Y}}
       case T1#T2
       of (literal(N1))#(literal(N2)) then {Push SemanticStack statement(st:[bind Z literal(N1*N2)] env: E)} {Main}
       else
	  {Exception.'raise' variableUnbound(add)}
       end
       end
    end

    % S = Stack and E = Environment
    proc {MainUtil S E}
	  case S.1 of
	     nil then {Main}
	  [] nop then {Nop}
	  [] var then  {Var statement(st:S.2 env:E)}
	  [] record then skip
	  [] bind then  {Bind statement(st:S.2 env:E)}
	  [] conditional then {Show conditional} {Conditonal statement(st:S.2 env:E)}
	  [] match then {Show match} {Match statement(st:S.2 env:E)}
	  [] apply then {Show apply} {Apply statement(st:S.2 env:E)}
	  [] proc1 then {Show proc1} {Proc S E}% {Proc statement(st:S.2 env:E)}
	  [] add then {Show add} {Add S.2.1 S.2.2.1 S.2.2.2.1 E} 
	  [] mul then {Show product} {Product S.2.1 S.2.2.1 S.2.2.2.1 E}
	  [] Y|Yr then {Push SemanticStack statement(st:S.2 env:E)} {Push SemanticStack statement(st:S.1 env:E)} {Main}
	  end
    end
 
    proc {Main}
      local T in
	 T = {Pop SemanticStack}
	 if T \= nil andthen T.st \= nil then
	    {Show 'statement:'}
	    {Show T.st}
	    {Show 'Environment for this statement i.e. before execution of this statement:'}
	    {Show T.env}
	    {Show 'SAS before executing this statement:'}
	    {Show {Zip {Dictionary.keys SAS} {Dictionary.items SAS}}}
	    %{File write(vs:[1 2 3 4 5]#{Dictionary.keys SAS}#{Dictionary.items SAS}#'\n')}
	 end
	 
	 
          case T of
            nil then skip
            [] statement(st:X env:E) then if X==nil then {Main} else {MainUtil X E} end
          end
      end
    end

   % {Push SemanticStack statement(st:[var ident(x) [proc1 [ident(y)] [[nop] ident(x) ident(y)]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [proc1 [ident(y)] [[nop] ident(x) ident(y)]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(q) [ [bind ident(q) literal(10)] [var ident(x) [var ident(z) [bind ident(z) [proc1 [ident(y)] [bind ident(x) ident(y)]]] [apply ident(z) ident(q)]]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(q) [ [bind ident(q) literal(10)] [var ident(x) [var ident(z) [bind ident(z) [proc1 [ident(y)] [bind ident(y) ident(q)]]] [apply ident(z) ident(x)]]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(f) []]] env:nil)}
    %====================NOT Working
    %{Push SemanticStack statement(st:[var ident(ay) [var ident(z) [var ident(q) [ [var ident(x) [[bind ident(x) [record literal(list) [[literal(1) ident(q)] [literal(2) [record literal(list) [[literal(1) ident(ay)] [literal(2) nil]]]]]]][[bind ident(z) [proc1 [ident(y)] [match ident(y) [record literal(list) [[literal(1) ident(f)] [literal(2) ident(r)]]] [[bind ident(f) literal(100)] [apply ident(z) ident(r)]] [nop]]]]] [apply ident(z) ident(x)]]]]]]] env:nil)}
    %====================NOT Working
   %{Push SemanticStack statement(st:[[var ident(x) [var ident(y) [var ident(x) [nop]]]][var ident(x) [nop]]] env:nil)}
   % {Push SemanticStack statement(st:[var ident(x) [bind ident(x) t][conditional ident(x) [var ident(y) [nop]] [var ident(z) [nop]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(z)] [bind ident(z) ident(y)] [bind ident(x) ident(y)]]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) [record literal(a) [[literal(1) ident(y)] [literal(2) literal(10)]]]] [bind ident(x) [record literal(a) [[literal(1) literal(69)] [literal(2) ident(z)]]]]]]]] env:nil)}
    
   % {Push SemanticStack statement(st:[var ident(z) [var ident(x) [bind ident(x) [record literal(a) [[literal(f1) ident(z)][literal(f2) literal(2)]]]] [match ident(x) [record literal(a)[[literal(f1) ident(y)][literal(f2) ident(z)]]] [var ident(b) [nop]] [var ident(c) [nop]]]][bind ident(z) literal(10)]] env:nil)}
%{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) [record literal(a) [[literal(1) literal(5)] [literal(2) ident(z)]]]] [bind ident(y) [record literal(a) [[literal(1) ident(z)] [literal(2) literal(10)]]]] [bind ident(x) ident(y)]]]]] env:nil)}
   %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [[bind ident(x) [record literal(p) [[literal(n) ident(y)]]]] [bind ident(y) [record literal(p) [[literal(n) ident(x)]]]] [bind ident(x) ident(y)] ]]] env:nil)}
   %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [[bind ident(x) [record literal(p) [[literal(n) ident(y)]]]] [bind ident(y) literal(69)]]]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(5)] [bind ident(y) literal(2)][mul ident(x) ident(y) ident(z)]]]]] env:nil)}
    {Push SemanticStack statement(st:[var ident(x) [bind ident(x) [record literal(test) [[literal(1) literal(1)] [literal(2) ident(x)]]] ]] env:nil)}
    %{Showr createWindow}
    %{Showr option(buffer size:50)}

    % Tests
    %1){Push SemanticStack statement(st:[[nop] [nop]] env:nil)}
    %{Push SemanticStack statement(st:[var ident(x) [var ident(y) [var ident(z) [bind ident(x) ident(y)] [bind ident(y) ident(z)] [bind ident(z) ident(x)][bind ident(x) [record literal(a) [[literal(1) ident(x)][literal(2) ident(y)]]]][bind ident(z) [record literal(a)[[literal(1) ident(y)][literal(2) ident(x)]]]][nop]]]]  env:nil)}
    %{Push SemanticStack statement(st:[var ident(w) [var ident(x) [var ident(y) [[bind ident(w) literal(10)][bind ident(x) [record literal(a)[[literal(1) ident(y)][literal(2) ident(w)]]]] [bind ident(y) literal(5)]   [match ident(x) [record literal(a)[[literal(1) ident(z)][literal(2) ident(p)]]] [var ident(t) [nop]] [var ident(f) [nop]]]   ]]]] env:nil)}
    {Main}
   
    {Show 'Hello123'}
    {Show ''}
    %{File close}
    %{Show 'Hello123'}
    %{Show {Dictionary.condGet 
    %{Push SemanticStack statement(st:[var ident(sum) [var ident(product) [bind ident(sum) [proc1 [ident(x) ident(y) ident(z)] [add ident(x) ident(y) ident(z)]]] [bind ident(product) [proc1 [ident(x) ident(y) idient(z)] [mul ident(x) ident(y) ident(z)]]]]] env:nil)}
