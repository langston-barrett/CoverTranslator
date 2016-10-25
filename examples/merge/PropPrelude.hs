module PropPrelude where 
import Property
import Simple

isSimpleValue :: Simple -> Prop
isSimpleValue x = 
  x === A \/ 
  x === B \/ 
  x === C

