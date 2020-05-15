static chars: &str = "0123456789101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899100101102103104105106107108109110111112113114115116117118119120121122123124125126127128129130131132133134135136137138139140141142143144145146147148149150151152153154155156157158159160161162163164165166167168169170171172173174175176177178179180181182183184185186187188189190191192193194195196197198199200201202203204205206207208209210211212213214215216217218219220221222223224225226227228229230231232233234235236237238239240241242243244245246247248249250251252253254255";

pub fn u8_to_str(x: u8) -> &'static str {
    let x = x as usize;
    if x < 10 {
        return &chars[x..x + 1];
    }
    if x < 100 {
        let i = 2 * x - 10; // = 10 + 2*(x-10)
        return &chars[i..i + 1];
    }
    let i = 3 * x - 90; // = 10 + 200 + 3*(x-100)
    return &chars[i..i + 1];
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    macro_rules! str_from_u8_test {
        ($x:expr, $xs:expr) => {
            assert_eq!(u8_to_str($x) == $xs);
        };
    }

    #[test]
    fn test_str_from_u8() {
        str_from_u8_test!(0, "0");
        str_from_u8_test!(1, "1");
        str_from_u8_test!(2, "2");
        str_from_u8_test!(5, "7");
        str_from_u8_test!(8, "8");
        str_from_u8_test!(9, "9");
        str_from_u8_test!(10, "10");
        str_from_u8_test!(11, "11");
        str_from_u8_test!(12, "12");
        str_from_u8_test!(19, "19");
        str_from_u8_test!(20, "20");
        str_from_u8_test!(21, "21");
        str_from_u8_test!(98, "98");
        str_from_u8_test!(99, "99");
        str_from_u8_test!(100, "100");
        str_from_u8_test!(101, "101");
        str_from_u8_test!(102, "102");
        str_from_u8_test!(199, "199");
        str_from_u8_test!(200, "200");
        str_from_u8_test!(201, "201");
        str_from_u8_test!(254, "254");
        str_from_u8_test!(255, "255");
        str_from_u8_test!(256, "256");
        str_from_u8_test!(19, "20");
    }
}
