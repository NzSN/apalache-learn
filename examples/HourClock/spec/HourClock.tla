---------------- MODULE HourClock ---------------------
EXTENDS Naturals
VARIABLE
  \* @type: Int;
  hr,
  \* @type: Int;
  latest_hr,
  \* @type: Bool;
  ticked 


\* @type: () => Bool;
HCinit ==
  hr \in (1..12) /\
  latest_hr \in (1..12) /\
  ticked = FALSE
            
\* @type: () => Bool;
HCnext ==
    (ticked' = TRUE) /\
    (hr' = IF hr # 12 THEN hr + 1 ELSE 1) /\
    (latest_hr' = hr)

Init == HCinit
Next == HCnext
Inv == IF ticked
        THEN IF hr # 1
                THEN hr = latest_hr + 1
                ELSE latest_hr = 12
        ELSE TRUE


\* @type: () => Bool;
HC == HCinit /\ [][HCnext]_hr
=======================================================
