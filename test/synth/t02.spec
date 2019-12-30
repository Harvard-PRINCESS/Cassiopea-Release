(* github issue #150 (unsatisfiable spec) *)
def interrupts_are_on  -> bool =  *irqen == 0b1
frame:
pre: interrupts_are_on() == false
post: interrupts_are_on() == true
