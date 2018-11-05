declare Len ListExist L1SubsetL2 GetIdentRecord
    fun {Len L}
      case L
      of nil then 0
      [] X|Xr then 1+{Len Xr}
      end
    end

    fun {ListExist L X}
      case L
      of nil then false
      [] X1|Xr then if X1.1==X.1 then true else {ListExist Xr X} end
      end
    end

    fun {L1SubsetL2 L1 L2}
        case L1
        of nil then true
        [] X|Xr then if {ListExist L2 X} then {L1SubsetL2 Xr L2} else false end
        end
    end

    fun {GetIdentRecord L X}
      case L
      of nil then nil
      [] Y|Yr then if Y.1==X then Y.2.1 else {GetIdentRecord Yr X} end
      end 
    end
    