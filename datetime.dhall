-- [leave them for nonce] consider removing DateTime/getYear DateTime/getMonth DateTime/getDay
-- get rid of roll (Prf can guarantee that we wont have out of range issues)
-- also try to use builtins as much as possible: conversions to and from unions suck!
-- also use direct calls instead of via other functions even if you have to have redundant code
-- DateTime/addDays is needed else way too slow
-- dont include tuple if possible cos of slowdowns
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude

let nz = ./nonzero.dhall
let nn = ./natural.dhall
let ii = ./integer.dhall
let oo = ./ordering.dhall

let Month : Type = < Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec >

let secondsInDay = +86400 : Integer
let secondsInDayNZ = !86400 : NonZero

let zeroTime =
    \(dt : DateTime)
 -> let x = NonZero/div (DateTime/toSeconds dt) secondsInDayNZ
    in Integer/multiply x secondsInDay
  : Integer

let fromMonth =
  \(m : Month)
  -> merge {
       , Jan = !1
       , Feb = !2
       , Mar = !3
       , Apr = !4
       , May = !5
       , Jun = !6
       , Jul = !7
       , Aug = !8
       , Sep = !9
       , Oct = !10
       , Nov = !11
       , Dec = !12
       } m
       : NonZero

let toMonthInternal =
    \(n : NonZero)
 -> if nz.equal n !1 then Month.Jan
     else if nz.equal n !2 then Month.Feb
     else if nz.equal n !3 then Month.Mar
     else if nz.equal n !4 then Month.Apr
     else if nz.equal n !5 then Month.May
     else if nz.equal n !6 then Month.Jun
     else if nz.equal n !7 then Month.Jul
     else if nz.equal n !8 then Month.Aug
     else if nz.equal n !9 then Month.Sep
     else if nz.equal n !10 then Month.Oct
     else if nz.equal n !11 then Month.Nov
     else if nz.equal n !12 then Month.Dec
     else PVoid/error ^^"datetime.dhall: toMonthInternal month is greater than 12" Month
     : Month

let toMonthProof =
    \(n : NonZero)
 -> \(prf : Proof/fromBool ^^"datetime.dhall toMonthProof n>12" (nz.lessThanEqual n !12))
 -> toMonthInternal n
   : Month

let getMonth =
   \(dt : DateTime)
 -> toMonthInternal (DateTime/fromDate dt).month
 : Month

let DayOfWeek = < Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday >

let toDayOfWeekInternal =
    \(n : Natural)
 -> if pp.Natural.equal n 0 then DayOfWeek.Monday
    else if pp.Natural.equal n 1 then DayOfWeek.Tuesday
    else if pp.Natural.equal n 2 then DayOfWeek.Wednesday
    else if pp.Natural.equal n 3 then DayOfWeek.Thursday
    else if pp.Natural.equal n 4 then DayOfWeek.Friday
    else if pp.Natural.equal n 5 then DayOfWeek.Saturday
    else if pp.Natural.equal n 6 then DayOfWeek.Sunday
    else PVoid/error ^^"datetime.dhall: toDayOfWeekInternal day is greater than 6" DayOfWeek
    : DayOfWeek

let fromDayOfWeekInternal =
    \(d : DayOfWeek)
 -> merge {
        Monday    = 0
      , Tuesday   = 1
      , Wednesday = 2
      , Thursday  = 3
      , Friday    = 4
      , Saturday  = 5
      , Sunday    = 6
      } d
   : Natural

let toDayOfWeekProof =
    \(n : Natural)
 -> \(prf : Proof/fromBool ^^"datetime.dhall toDayOfWeekProof n>6" (pp.Natural.lessThanEqual n 6))
 -> toDayOfWeekInternal n
   : DayOfWeek

let dayOfWeekInternal =
    \(dt : DateTime)
 -> let r = NonZero/div (zeroTime dt) secondsInDayNZ
    let s = Integer/add r +3
    let t = NonZero/mod s !7
    in pp.Integer.abs t
    : Natural

let dayOfWeek =
    \(dt : DateTime)
 -> toDayOfWeekInternal (dayOfWeekInternal dt)
    : DayOfWeek

let hmsInSeconds =
    \(dt : DateTime)
 -> let e = DateTime/toSeconds dt
    let f = zeroTime dt
    in pp.Integer.abs (ii.minus e f)
    : Natural

let getHH =
    \(dt : DateTime)
 -> nn.div (hmsInSeconds dt) !3600
    : Natural

let getMM =
    \(dt : DateTime)
 -> let a = nn.mod (hmsInSeconds dt) !3600
    in nn.div a !60
    : Natural

let getSS =
    \(dt : DateTime)
 -> let a = nn.mod (hmsInSeconds dt) !3600
    in nn.mod a !60
    : Natural

let getHMS =
    \(dt : DateTime)
 -> let a = nn.divMod (hmsInSeconds dt) !3600
    let b = nn.divMod a._2 !60
    in { _1 = a._1, _2 = b._1, _3 = b._2 }
    : { _1 : Natural, _2 : Natural, _3 : Natural }

let compare = oo.compareDateTime

let equal =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> oo.isEQ (compare dt1 dt2)
  : Bool

let lessThan =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> oo.isLT (compare dt1 dt2)
  : Bool

let lessThanEqual =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> oo.isLE (compare dt1 dt2)
  : Bool

let greaterThan =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> oo.isGT (compare dt1 dt2)
  : Bool

let greaterThanEqual =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> oo.isGE (compare dt1 dt2)
  : Bool

let compareMonth =
    \(m1 : Month)
 -> \(m2 : Month)
 -> nz.compare (fromMonth m1) (fromMonth m2)
  : oo.Ordering

let equalMonth =
    \(m1 : Month)
 -> \(m2 : Month)
 -> oo.isEQ (compareMonth m1 m2)
  : Bool

let compareDayOfWeek =
    \(d1 : DayOfWeek)
 -> \(d2 : DayOfWeek)
 -> nn.compare (fromDayOfWeekInternal d1) (fromDayOfWeekInternal d2)
  : oo.Ordering

let equalDayOfWeek =
    \(d1 : DayOfWeek)
 -> \(d2 : DayOfWeek)
 -> oo.isEQ (compareDayOfWeek d1 d2)
  : Bool

let diffSeconds =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> ii.minus (DateTime/toSeconds dt1) (DateTime/toSeconds dt2)
  : Integer

let diffDays =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> let a = diffSeconds dt1 dt2
    let b = NonZero/div (if pp.Integer.negative a then Integer/negate a else a) secondsInDayNZ
    in if pp.Integer.negative a then Integer/negate b else b
    : Integer

let diffDaysAbs =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> let a = ii.minus (zeroTime dt1) (zeroTime dt2)
    in NonZero/div a secondsInDayNZ
    : Integer

let addSeconds =
     \(n : Integer)
  -> \(dt : DateTime)
  -> DateTime/fromSeconds (Integer/add n (DateTime/toSeconds dt))
     : DateTime

let addMinutes =
     \(n : Integer)
  -> \(dt : DateTime)
  -> addSeconds (Integer/multiply n +60) dt
     : DateTime

let addHours =
     \(n : Integer)
  -> \(dt : DateTime)
  -> addSeconds (Integer/multiply n +3600) dt
     : DateTime

let addWeeks =
     \(n : Integer)
  -> \(dt : DateTime)
  -> DateTime/addDays (Integer/multiply n +7) dt
     : DateTime

let setHourProof =
     \(n : Natural)
  -> \(dt : DateTime)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setHourProof n>23" (pp.Natural.lessThanEqual n 23))
  -> let a = Natural/toInteger n
     let b = Natural/toInteger (getHH dt)
     in addHours (ii.minus a b) dt
     : DateTime

let setMinuteProof =
     \(n : Natural)
  -> \(dt : DateTime)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setMinuteProof n>59" (pp.Natural.lessThanEqual n 59))
  -> let a = Natural/toInteger n
     let b = Natural/toInteger (getMM dt)
     in addMinutes (ii.minus a b) dt
     : DateTime

let setSecondProof =
     \(n : Natural)
  -> \(dt : DateTime)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setSecondProof n>59" (pp.Natural.lessThanEqual n 59))
  -> let a = Natural/toInteger n
     let b = Natural/toInteger (getSS dt)
     in addSeconds (ii.minus a b) dt
     : DateTime

let setYear =
     \(n : Integer)
  -> \(dt : DateTime)
  -> DateTime/addYears (ii.minus n (DateTime/fromDate dt).year) dt
   : DateTime

let setMonth =
     \(n : Month)
  -> \(dt : DateTime)
  -> let a = NonZero/toInteger (fromMonth n)
     let b = NonZero/toInteger (DateTime/fromDate dt).month
     in DateTime/addMonths (ii.minus a b) dt
   : DateTime

let lastDayOfMonth =
     \(dt : DateTime)
  -> let z = DateTime/fromDate dt
     in DateTime/lastDayOfMonth z.year z.month
     : NonZero

let setDayProof =
     \(n : NonZero)
  -> \(dt : DateTime)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setDayProof day out of range" (nz.lessThanEqual n (lastDayOfMonth dt)))
  -> let a = NonZero/toInteger n
     let b = NonZero/toInteger (DateTime/fromDate dt).day
     in DateTime/addDays (ii.minus a b) dt
     : DateTime

let setDateTimeProof =
     \(y : Integer)
  -> \(m : Month)
  -> \(d : NonZero)
  -> \(hh : Natural)
  -> \(mm : Natural)
  -> \(ss : Natural)
  -> \(prf1 : Proof/fromBool ^^"datetime.dhall setDateTimeProof day is out of range" (nz.lessThanEqual d (DateTime/lastDayOfMonth y (fromMonth m))))
  -> \(prf2 : Proof/fromBool ^^"datetime.dhall setDateTimeProof hour/min/sec is out of range" (pp.Natural.lessThanEqual hh 23 && pp.Natural.lessThanEqual mm 59 && pp.Natural.lessThanEqual ss 59))
  -> DateTime/toDate y (fromMonth m) d hh mm ss
    : DateTime

let setDateProof =
     \(y : Integer)
  -> \(m : Month)
  -> \(d : NonZero)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setDateProof day is out of range" (nz.lessThanEqual d (DateTime/lastDayOfMonth y (fromMonth m))))
  -> setDateTimeProof y m d 0 0 0 prf Prf
    : DateTime

let getDateTime =
     \(dt : DateTime)
  -> let z = DateTime/fromDate dt
     in z // { month = toMonthInternal z.month }

let isLeapYear =
    \(y : Integer)
  -> let a = DateTime/lastDayOfMonth y !2
     in nz.equal a !29
     : Bool

let gotoLastDayOfMonth =
    \(dt : DateTime)
 -> let a = lastDayOfMonth dt
    let b = (DateTime/fromDate dt).day
    let c = nz.subtractInternal b a
    in DateTime/addDays (NonZero/toInteger c) dt
    : DateTime

let firstDayOfMonth =
    \(y : Integer)
 -> \(m : Month)
 -> \(d : DayOfWeek)
 -> let x = DateTime/toDate y (fromMonth m) !1 0 0 0
    let b = dayOfWeekInternal x
    let c = fromDayOfWeekInternal d
    let w = if pp.Natural.greaterThanEqual c b then Natural/subtract b c
            else Natural/subtract b (c + 7)
    in DateTime/addDays (Natural/toInteger w) x
    : DateTime

-- not as slow but noticeable difference
let allDaysMonth =
    \(y : Integer)
 -> \(m : Month)
 -> \(d : DayOfWeek)
 -> let x0 = firstDayOfMonth y m d : DateTime
    let x4 = DateTime/addDays +28 x0
    let rs = [x0, DateTime/addDays +7 x0, DateTime/addDays +14 x0, DateTime/addDays +21 x0]
    in if nz.equal (DateTime/fromDate x4).month (fromMonth m) then rs # [x4] else rs
     : List DateTime

-- we only get the week number back so need to calculate the effective year
-- if 52/53 weeks and jan then we know it is the previous year
-- if week 1 but in december then must be next year
-- otherwise current year cos not on the edge
-- the algorithm for this is crazy: if the Monday is 4 days over the year or more then that year ...
let toWeekDate =
     \(dt : DateTime)
  -> let z = DateTime/toWeek dt
     in { year = z.year, week = z.week, day = toDayOfWeekInternal z.day }

-- some years have 53 weeks and some have only 52 but the proof is close enuf
let fromWeekDateProof =
     \(y : Integer)
  -> \(w : NonZero)
  -> \(d : DayOfWeek)
  -> \(prf : Proof/fromBool ^^"datetime.dhall fromWeekDateProof n>53" (nz.lessThanEqual w !53))
  -> DateTime/fromWeek y w (NonZero/clamp (1 + fromDayOfWeekInternal d))
     : DateTime

let setJulianDayProof =
     \(y : Integer)
  -> \(d : NonZero)
  -> \(prf : Proof/fromBool ^^"datetime.dhall setJulianDate day>365 or 366 if leapyear" (nz.lessThanEqual d (if isLeapYear y then !366 else !365)))
  -> DateTime/setJulianDay y d
   : DateTime

let min =
    \(m : DateTime)
 -> \(n : DateTime)
 -> if greaterThan m n then n else m
  : DateTime

let max =
    \(m : DateTime)
 -> \(n : DateTime)
 -> if greaterThan m n then m else n
  : DateTime

let test1 = assert : toWeekDate ^2020-01-01T20:01:12 === { year = +2020, week = !1, day = DayOfWeek.Wednesday }
let test2 = assert : toWeekDate ^2019-12-31T23:59:00 === { year = +2020, week = !1, day = DayOfWeek.Tuesday }
let test3 = assert : fromWeekDateProof +2020 !1 DayOfWeek.Wednesday Prf === ^2020-01-01
let test4 = assert : fromWeekDateProof  +2020 !1 DayOfWeek.Tuesday Prf === ^2019-12-31

let test5 = assert : toWeekDate ^2016-01-04T20:01:12 === { year = +2016, week = !1, day = DayOfWeek.Monday }
let test6 = assert : toWeekDate ^2016-01-01T20:01:12 === { year = +2015, week = !53, day = DayOfWeek.Friday }
let test7 = assert : toWeekDate ^2015-12-31T23:59:00 === { year = +2015, week = !53, day = DayOfWeek.Thursday }
let test8 = assert : fromWeekDateProof  +2016 !1 DayOfWeek.Monday Prf === ^2016-01-04
let test9 = assert : fromWeekDateProof  +2015 !53 DayOfWeek.Friday Prf === ^2016-01-01
let test10 = assert : fromWeekDateProof  +2015 !53 DayOfWeek.Thursday Prf === ^2015-12-31

let test11 = assert : toWeekDate ^2020-02-25 === { year = +2020, week = !9, day = DayOfWeek.Tuesday }
let test12 = assert : fromWeekDateProof +2020 !9 DayOfWeek.Tuesday Prf === ^2020-02-25

let test13 = assert : toWeekDate ^2017-01-02 === { year = +2017, week = !1, day = DayOfWeek.Monday }
let test14 = assert : toWeekDate ^2017-01-01 === { year = +2016, week = !52, day = DayOfWeek.Sunday }
let test15 = assert : toWeekDate ^2016-12-31 === { year = +2016, week = !52, day = DayOfWeek.Saturday }
let test16 = assert : toWeekDate ^2016-12-26 === { year = +2016, week = !52, day = DayOfWeek.Monday }
let test17 = assert : fromWeekDateProof +2017 !1 DayOfWeek.Monday Prf === ^2017-01-02
let test18 = assert : fromWeekDateProof +2016 !52 DayOfWeek.Sunday Prf === ^2017-01-01
let test19 = assert : fromWeekDateProof  +2016 !52 DayOfWeek.Saturday Prf === ^2016-12-31
let test20 = assert : fromWeekDateProof  +2016 !52 DayOfWeek.Monday Prf === ^2016-12-26

let test21 = assert : toWeekDate ^2016-01-04 === { year = +2016, week = !1, day = DayOfWeek.Monday }
let test22 = assert : toWeekDate ^2016-01-01 === { year = +2015, week = !53, day = DayOfWeek.Friday }
let test23 = assert : toWeekDate ^2015-12-31 === { year = +2015, week = !53, day = DayOfWeek.Thursday }
let test24 = assert : fromWeekDateProof +2016 !1 DayOfWeek.Monday Prf === ^2016-01-04
let test25 = assert : fromWeekDateProof +2015 !53 DayOfWeek.Friday Prf === ^2016-01-01
let test26 = assert : fromWeekDateProof  +2015 !53 DayOfWeek.Thursday Prf === ^2015-12-31

let test27 = assert : dayOfWeek ^2020-01-20T20:01:12 === DayOfWeek.Monday
let test28 = assert : dayOfWeek ^1970-01-01T20:01:12 === DayOfWeek.Thursday
let test29 = assert : dayOfWeek ^1969-12-31T20:01:12 === DayOfWeek.Wednesday
let test30 = assert : dayOfWeek ^1844-09-17 === DayOfWeek.Tuesday
let test31 = assert : getSS ^1969-12-31T20:01:12 === 12
let test32 = assert : getMM ^1969-12-31T20:55:12 === 55
let test33 = assert : getHH ^1969-12-31T20:01:12 === 20
let test34 = assert : getMonth ^1969-12-31T20:01:12 === Month.Dec
let test35 = assert : DateTime/fromDate ^1969-12-31T20:01:13 === { year = +1969, month = !12, day = !31, hour = 20, minute = 1, second = 13 }
let test36 = assert : DateTime/addDays +3 ^1969-12-11T20:01:12 === ^1969-12-14T20:01:12
let test37 = assert : DateTime/addDays -20 ^1969-12-11T20:01:12 === ^1969-11-21T20:01:12
let test38 = assert : DateTime/addMonths +3 ^1969-12-11T20:01:12 === ^1970-03-11T20:01:12
let test39 = assert : DateTime/addYears -3 ^1969-12-11T20:01:12 === ^1966-12-11T20:01:12
let test40 = assert : DateTime/addYears -2 ^1972-02-29T20:01:12 === ^1970-02-28T20:01:12
let test41 = assert : addHours -3 ^1969-12-11T20:01:12 === ^1969-12-11T17:01:12
let test42 = assert : addHours +30 ^2020-05-11T03:01:12 === ^2020-05-12T09:01:12
let test43 = assert : addMinutes +12 ^2020-05-11T03:01:12 === ^2020-05-11T03:13:12
let test44 = assert : addSeconds +50 ^2020-05-11T03:01:12 === ^2020-05-11T03:02:02

let test45 = assert : setHourProof 14 ^1969-12-11T20:01:12 Prf === ^1969-12-11T14:01:12

--let test31 = assert : setHourProof 55 ^1969-12-11T20:01:12 Prf === ^1969-12-13T07:01:12
-- proof fails if outofrange
let test46 = assert : setHourProof 12 ^1969-12-11T20:01:12 Prf === ^1969-12-11T12:01:12
let test47 = assert : setMinuteProof 59 ^1969-12-11T20:01:12 Prf === ^1969-12-11T20:59:12
let test48 = assert : setSecondProof 0 ^1969-12-11T20:01:12 Prf === ^1969-12-11T20:01:00

let test49 = assert : setMinuteProof 22 ^1990-05-30T00:14:59 Prf === ^1990-05-30T00:22:59
let test50 = assert : setSecondProof 22 ^1990-05-30T00:14:59 Prf === ^1990-05-30T00:14:22

let test51 = assert : setYear +2020 ^1969-12-11T20:01:12 === ^2020-12-11T20:01:12
let test52 = assert : (DateTime/fromDate (setYear -7 ^3)).year === -7

let test53 = assert : setMonth Month.Sep ^1969-12-11T20:01:12 === ^1969-09-11T20:01:12
let test54 = assert : setDayProof !3 ^1984-12-11T20:01:12 Prf === ^1984-12-03T20:01:12
let test55 = assert : setDayProof !31 ^1984-12-11T20:01:12 Prf === ^1984-12-31T20:01:12

-- let test42 = assert : setDayProof !32 ^1984-12-11T20:01:12 Prf === ^1985-01-01T20:01:12

let test56 = assert : setDayProof !30 ^1984-12-11T20:01:12 Prf === ^1984-12-30T20:01:12
let test57 = assert : setDayProof !31 ^1984-12-11T20:01:12 Prf === ^1984-12-31T20:01:12

let test58 = assert : ^-3 === ^-3-01-01T00:00:00
let test59 = assert : setYear -20 ^-2014-12-11T12:13:44 === ^-20-12-11T12:13:44
let test60 = assert : setYear +1923 ^-2014-12-11T12:13:44 === ^1923-12-11T12:13:44

let test61 = assert : DateTime/fromSeconds (zeroTime ^2020-12-12T14:12:13) === ^2020-12-12
let test62 = assert : lastDayOfMonth ^2020-12 === !31
let test63 = assert : lastDayOfMonth ^2020-02 === !29
let test64 = assert : lastDayOfMonth ^1900-02 === !28
let test65 = assert : setDateProof +1964 Month.Sep !14 Prf === ^1964-09-14
let test66 = assert : getSS (setDateProof +1964 Month.Sep !14 Prf) === 0
let test67 = assert : getSS (setDateProof +2020 Month.Jan !30 Prf) === 0
let test68 = assert : getSS (^2020-07-01T12:13:15) === 15
let test69 = assert : getSS (^2020-07-14T12:13:59) === 59
let test70 = assert : isLeapYear +2020 === True
let test71 = assert : isLeapYear +1900 === False
let test72 = assert : isLeapYear +2019 === False

let test73 = assert : DateTime/getJulianDay ^2020-01-21 === !21
let test74 = assert : DateTime/getJulianDay ^2020-02-21 === !52
let test75 = assert : DateTime/setJulianDay +2020 !52 === ^2020-02-21
let test76 = assert : DateTime/getJulianDay (DateTime/setJulianDay +1965 !173) === !173
let test77 = assert : DateTime/setJulianDay +1965 !173 === ^1965-06-22T00:00:00
let test78 = assert : setJulianDayProof +1965 !173 Prf === ^1965-06-22T00:00:00
let test79 = assert : setJulianDayProof +2020 !366 Prf === ^2020-12-31

let test80 = assert : setJulianDayProof +2020 !365 Prf === ^2020-12-30T00:00:00

let test81 = assert : setJulianDayProof +2020 !366 Prf === ^2020-12-31T00:00:00

-- setJulianDayProof +2020 !367 Prf
-- setJulianDayProof +2019 !366 Prf
let test82 = assert : setJulianDayProof +2019 !365 Prf === ^2019-12-31T00:00:00

-- overflow just makes it equivalient to last day of year
let test83 = assert : DateTime/setJulianDay +1965 !401 === ^1965-12-31T00:00:00
-- underflow just makes it equivalient to last day of year
let test84 = assert : DateTime/setJulianDay +1965 !1 === ^1965-01-01T00:00:00
let test85 = assert : diffDays ^1965-01-31 ^1965-01-31 === +0
let test86 = assert : diffDays ^1965-01-31 ^1964-11-14 === +78
let test87 = assert : diffDays ^1964-11-14 ^1965-01-31 === -78

let test88 = assert : diffDays ^1964-11-14T23:59:59 ^1964-11-15T00:00:01 === -0
let test89 = assert : diffDays ^2020-11-14T23:59:59 ^2020-11-15T00:00:01 === -0

let test90 = assert : diffDays ^1964-11-15T00:00:01 ^1964-11-14T23:59:59 === +0
let test91 = assert : diffDays ^2020-11-15T00:00:01 ^2020-11-14T23:59:59 === +0

let test92 = assert : diffDaysAbs ^1964-11-14T23:59:59 ^1964-11-15T00:00:01 === -1
let test93 = assert : diffDaysAbs ^2020-11-14T23:59:59 ^2020-11-15T00:00:01 === -1

let test94 = assert : diffDaysAbs ^1964-11-15T00:00:01 ^1964-11-14T23:59:59 === +1
let test95 = assert : diffDaysAbs ^2020-11-15T00:00:01 ^2020-11-14T23:59:59 === +1

let test96 = assert : DateTime/parse "-2001-04-09" === Some ^-2001-04-09T00:00:00
-- clips the day cos not a leap year
let test97 = assert : setYear +1923 ^-2000-02-29T12:13:44 === ^1923-02-28T12:13:44
let test98 = assert : setYear +1980 ^-2000-02-29T12:13:44 === ^1980-02-29T12:13:44
let test99 = assert : setDayProof !13 ^2020-02 Prf === ^2020-02-13T00:00:00
let test100 = assert : setDayProof !29 ^2020-02 Prf === ^2020-02-29T00:00:00
--let test83 = assert : setDayProof !29 ^2019-02 Prf === ^2019-03-01T00:00:00

let test101 = assert : DateTime/parse "-2020-10-12" === Some ^-2020-10-12T00:00:00
let test102 = assert : DateTime/parse "-2020-10-99T00:00:00" === None DateTime
let test103 = assert : DateTime/parse "-2020-10-12T00:00:59" === Some ^-2020-10-12T00:00:59
let test104 = assert : DateTime/parse "-2020-10-12T00:00:60" === None DateTime
let test105 = assert : DateTime/parse "-2020-10-12T00:60:00" === None DateTime
let test106 = assert : DateTime/parse "-2020-10-12T69:12:10" === None DateTime

let test107 = assert : setDayProof !30 (setMonth Month.Jan (setYear +2020 ^0)) Prf === ^2020-01-30

let test108 = assert : setDateProof +0 Month.Jan !1 Prf === ^0-01-01T00:00:00

let test109 = assert : ^T11:13:59 === ^1970-01-01T11:13:59
let test110 = assert : ^11:13:59 === ^1970-01-01T11:13:59

let test111 = assert : ^T11:13 === ^1970-01-01T11:13:00
let test112 = assert : ^11:13 === ^1970-01-01T11:13:00

let test113 = assert : ^T11 === ^1970-01-01T11:00:00

let test114 = assert : ^12-05-29T01:13:59 === ^12-05-29T01:13:59
let test115 = assert : ^12-05-29T01:13 === ^12-05-29T01:13:00
let test116 = assert : ^12-05-29T01 === ^12-05-29T01:00:00
let test117 = assert : ^12-05-29 === ^12-05-29T00:00:00

let test118 = assert : ^12-05T01:13:59 === ^12-05-01T01:13:59
let test119 = assert : ^12-05T01:13 === ^12-05-01T01:13:00
let test120 = assert : ^12-05T01 === ^12-05-01T01:00:00
let test121 = assert : ^12-05 === ^12-05-01T00:00:00

let test122 = assert : ^12T01:13:59 === ^12-01-01T01:13:59
let test123 = assert : ^12T01:13 === ^12-01-01T01:13:00
let test124 = assert : ^12T01 === ^12-01-01T01:00:00
let test125 = assert : ^12 === ^12-01-01T00:00:00

let test126 = assert : ^+2020 === ^2020-01-01T00:00:00
let test127 = assert : ^2020 === ^2020-01-01T00:00:00
let test128 = assert : ^-2020 === ^-2020-01-01T00:00:00

let test129 = assert : compareMonth Month.Jan Month.Dec === oo.LT
let test130 = assert : compareMonth Month.Dec Month.Jan === oo.GT
let test131 = assert : firstDayOfMonth +2020 Month.Feb DayOfWeek.Tuesday === ^2020-02-04

let test132 = assert : allDaysMonth +2020 Month.Feb DayOfWeek.Tuesday ===
[ ^2020-02-04T00:00:00
, ^2020-02-11T00:00:00
, ^2020-02-18T00:00:00
, ^2020-02-25T00:00:00
]

let test133 = assert : allDaysMonth +2020 Month.Mar DayOfWeek.Tuesday ===
[ ^2020-03-03T00:00:00
, ^2020-03-10T00:00:00
, ^2020-03-17T00:00:00
, ^2020-03-24T00:00:00
, ^2020-03-31T00:00:00
]

let test134 = assert : allDaysMonth +2020 Month.Mar DayOfWeek.Friday ===
[ ^2020-03-06T00:00:00
, ^2020-03-13T00:00:00
, ^2020-03-20T00:00:00
, ^2020-03-27T00:00:00
]

--let test108 = assert : weekOfYearOLD +2020 DayOfWeek.Monday 4 === ^2020-02-03T00:00:00

let test135 = assert : compareDayOfWeek DayOfWeek.Monday DayOfWeek.Tuesday === oo.LT
let test136 = assert : compareDayOfWeek DayOfWeek.Sunday DayOfWeek.Sunday === oo.EQ
let test137 = assert : compareDayOfWeek DayOfWeek.Sunday DayOfWeek.Monday === oo.GT

let test138 = assert : toMonthProof !3 Prf === Month.Mar
--let test109 = assert : toMonthProof !13 Prf === Month.Mar
let test139 = assert : toDayOfWeekProof 0 Prf === DayOfWeek.Monday
let test140 = assert : toDayOfWeekProof 6 Prf === DayOfWeek.Sunday
--let test109 = assert : toDayOfWeekProof 7 Prf === DayOfWeek.Sunday

let test141 = assert : setDateProof +2020 Month.Feb !29 Prf === ^2020-02-29T00:00:00
--let test78 = assert : setDateProof +2020 Month.Feb !30 Prf === ^2020-02-29T00:00:00

let test142 =
   let dt = ^2020-02-29T14:23:59
   let z = DateTime/fromDate dt
   let test1 = assert : z.hour === 14
   let test2 = assert : z.minute === 23
   let test3 = assert : z.second === 59
   let test4 = assert : getHMS dt === { _1 = 14, _2 = 23, _3 = 59 }
   let test5 = assert : hmsInSeconds dt === 51839
   let test6 = assert : z.year === +2020
   let test7 = assert : getMonth dt === Month.Feb
   let test8 = assert : toMonthProof z.month Prf === Month.Feb
   let test8 = assert : toMonthInternal z.month === Month.Feb
   let test8 = assert : z.day === !29
   let test9 = assert : dayOfWeek dt === DayOfWeek.Saturday
   let test10 = assert : lastDayOfMonth dt === !29
   let test11 = assert : lastDayOfMonth (DateTime/addDays +1 dt) === !31
   let test12 = assert : lastDayOfMonth (DateTime/addMonths +2 dt) === !30
   in {=}

let test143 = assert : DateTime/fromDate ^2020-02-29T12:13:14 === { year = +2020, month = !2, day = !29, hour = 12, minute = 13, second =14 }
let test144 = assert : DateTime/toDate +2020 !2 !29 12 13 14 === ^2020-02-29T12:13:14
let test145 = assert : DateTime/toDate +2020 !13 !40 99 99 99 === ^2020-12-31T23:59:59
let test146 = assert : DateTime/toDate +2020 !13 !4 22 99 13 === ^2020-12-04T22:59:13

let test147 = assert : getDateTime ^2020-02-29T12:13:14 === { year = +2020, month = Month.Feb, day = !29, hour = 12, minute = 13, second =14 }
let test148 = assert : setDateTimeProof +2020 Month.Feb !29 12 13 14 Prf Prf === ^2020-02-29T12:13:14

let test149 = assert : dayOfWeekInternal ^2020-02-29T23:59:59 === 5
let test150 = assert : dayOfWeekInternal ^2020-03-01 === 6
let test151 = assert : dayOfWeekInternal ^1970-01-01 === 3

let test152 = assert : toMonthInternal !1 === Month.Jan
let test153 = assert : toMonthInternal !12 === Month.Dec

in {
, dayOfWeek
, DayOfWeek

, Monday    = DayOfWeek.Monday
, Tuesday   = DayOfWeek.Tuesday
, Wednesday = DayOfWeek.Wednesday
, Thursday  = DayOfWeek.Thursday
, Friday    = DayOfWeek.Friday
, Saturday  = DayOfWeek.Saturday
, Sunday    = DayOfWeek.Sunday

, toDayOfWeekProof
, hmsInSeconds
, getHH
, getMM
, getSS
, getHMS
, toMonthProof
, fromMonth

, Month

, Jan = Month.Jan
, Feb = Month.Feb
, Mar = Month.Mar
, Apr = Month.Apr
, May = Month.May
, Jun = Month.Jun
, Jul = Month.Jul
, Aug = Month.Aug
, Sep = Month.Sep
, Oct = Month.Oct
, Nov = Month.Nov
, Dec = Month.Dec

, getMonth
, diffSeconds
, addWeeks
, addHours
, addMinutes
, addSeconds

, setYear
, setMonth
, setDayProof
, zeroTime
, isLeapYear
, lastDayOfMonth
, setDateProof
, setDateTimeProof
, getDateTime
, diffDays
, diffDaysAbs

, equal

, lessThanEqual
, lessThan
, greaterThanEqual
, greaterThan

, compare

, equalMonth
, compareMonth
, equalDayOfWeek
, compareDayOfWeek

, firstDayOfMonth
, allDaysMonth
, gotoLastDayOfMonth

, toWeekDate
, fromWeekDateProof

, setJulianDayProof

, min
, max
}
