//! The formats that are asserted.
//!
//! A format is modelled when the strings that it accepts are a regular language that can be
//! written down exactly. Each such format is one pattern here, in the dialect of the `regex`
//! crate, built from the grammar of the document that defines the format. Any other format is
//! a predicate that the engine does not model.
//!
//! Three formats are modelled in part: of some strings the pattern says that the format
//! accepts them, a second pattern holds the strings that it may accept, and all the rest it
//! rejects. That is for strings of which no grammar says whether they are of the format, and
//! for strings that the grammar of the format allows and that validators do not take.
//!
//! A digit is one of ASCII in every format, so the patterns say `[0-9]` and never `\d`.

/// A format as the engine models it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Format {
    /// The strings that the format accepts, as a pattern.
    pub accepted: &'static str,
    /// The strings that the format may accept, as a pattern: of those of them that the
    /// pattern above does not hold, it is not modelled whether the format accepts them.
    /// Without this, the pattern above is all that the format accepts.
    pub open: Option<&'static str>,
}

/// How a format is modelled, if it is.
pub(crate) fn modelled(format: &str) -> Option<Format> {
    let whole = |accepted| Format {
        accepted,
        open: None,
    };
    Some(match format {
        "date" => whole(DATE),
        "time" => Format {
            accepted: TIME,
            open: Some(TIME_WITH_SECOND_60),
        },
        "date-time" => Format {
            accepted: DATE_TIME,
            open: Some(DATE_TIME_WITH_SECOND_60),
        },
        "duration" => Format {
            accepted: DURATION,
            open: Some(DURATION_IN_EITHER_CASE),
        },
        "uuid" => whole(UUID),
        "ipv4" => whole(IPV4),
        "ipv6" => whole(IPV6),
        "uri" => whole(URI),
        "uri-reference" => whole(URI_REFERENCE),
        "json-pointer" => whole(JSON_POINTER),
        "relative-json-pointer" => whole(RELATIVE_JSON_POINTER),
        _ => return None,
    })
}

/// The whole string is this and nothing else.
macro_rules! whole {
    ($($part:expr),+ $(,)?) => {
        concat!("^(?:", $($part),+, ")$")
    };
}

// RFC 3339, section 5.6: `full-date`, with the days that each month has. February has 29 in
// a year that four divides, unless a hundred divides it and four hundred does not.
macro_rules! leap_year {
    () => {
        "(?:[0-9]{2}(?:0[48]|[2468][048]|[13579][26])|(?:[02468][048]|[13579][26])00)"
    };
}
macro_rules! date {
    () => {
        concat!(
            "(?:[0-9]{4}-(?:",
            "(?:0[13578]|1[02])-(?:0[1-9]|[12][0-9]|3[01])",
            "|(?:0[469]|11)-(?:0[1-9]|[12][0-9]|30)",
            "|02-(?:0[1-9]|1[0-9]|2[0-8])",
            ")|",
            leap_year!(),
            "-02-29)"
        )
    };
}
const DATE: &str = whole!(date!());

// RFC 3339, section 5.6: `full-time`, with a second from 00 to 59.
//
// The grammar lets the second be 60 too, "based on leap second rules": a leap second is the
// last second of a day of UTC, and only of the few days that had one. Which strings with the
// second 60 are times is therefore not for a pattern to say, and the second pattern holds
// them all: a time, with 60 for its second.
macro_rules! time {
    ($second:literal) => {
        concat!(
            "(?:[01][0-9]|2[0-3]):[0-5][0-9]:",
            $second,
            r"(?:\.[0-9]+)?(?:[Zz]|[+-](?:[01][0-9]|2[0-3]):[0-5][0-9])"
        )
    };
}
const TIME: &str = whole!(time!("[0-5][0-9]"));
const TIME_WITH_SECOND_60: &str = whole!(time!("60"));

// RFC 3339, section 5.6: `date-time`.
const DATE_TIME: &str = whole!(date!(), "[Tt]", time!("[0-5][0-9]"));
const DATE_TIME_WITH_SECOND_60: &str = whole!(date!(), "[Tt]", time!("60"));

// RFC 3339, appendix A: `duration`, with the letters as the grammar writes them.
//
// The grammar is ABNF, in which a letter in quotes stands for both of its cases, so by the
// letter `p1d` is a duration too. Validators take the capital letters only. So of a duration
// with a small letter it is left open whether it is one, and the second pattern holds a
// duration in either case.
macro_rules! duration_time {
    ($t:literal, $h:literal, $m:literal, $s:literal) => {
        concat!(
            $t,
            "(?:[0-9]+",
            $h,
            "(?:[0-9]+",
            $m,
            "(?:[0-9]+",
            $s,
            ")?)?",
            "|[0-9]+",
            $m,
            "(?:[0-9]+",
            $s,
            ")?",
            "|[0-9]+",
            $s,
            ")"
        )
    };
}
macro_rules! duration {
    ($p:literal, $y:literal, $m:literal, $w:literal, $d:literal, $t:literal, $h:literal, $s:literal) => {
        concat!(
            $p,
            "(?:",
            "(?:[0-9]+",
            $d,
            "|[0-9]+",
            $m,
            "(?:[0-9]+",
            $d,
            ")?",
            "|[0-9]+",
            $y,
            "(?:[0-9]+",
            $m,
            "(?:[0-9]+",
            $d,
            ")?)?)",
            "(?:",
            duration_time!($t, $h, $m, $s),
            ")?",
            "|",
            duration_time!($t, $h, $m, $s),
            "|[0-9]+",
            $w,
            ")"
        )
    };
}
const DURATION: &str = whole!(duration!("P", "Y", "M", "W", "D", "T", "H", "S"));
const DURATION_IN_EITHER_CASE: &str = whole!(duration!(
    "[Pp]", "[Yy]", "[Mm]", "[Ww]", "[Dd]", "[Tt]", "[Hh]", "[Ss]"
));

// RFC 4122, section 3.
const UUID: &str =
    whole!("[0-9A-Fa-f]{8}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{12}");

// RFC 2673, section 3.2: four numbers up to 255, none with a zero before it. That is also
// what RFC 3986 takes for an address inside an IPv6 address and inside a URI.
//
// The grammar of RFC 2673 gives a number one to three digits, so by the letter `01.2.3.4`
// is an address too. The pattern is narrower than the grammar here, and it is the one place
// where a pattern is: the corpus has `087.10.0.1` as no address, as the test suite that it
// is made from, and validators do not take a number with a zero before it, which some
// programs read as octal. The library follows them.
macro_rules! ipv4 {
    () => {
        r"(?:(?:25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])\.){3}(?:25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])"
    };
}
const IPV4: &str = whole!(ipv4!());

// RFC 4291, section 2.2, as RFC 3986 writes it out in `IPv6address`: eight groups, of which
// `::` stands for one or more, and the last two may be an IPv4 address.
macro_rules! h16 {
    () => {
        "[0-9A-Fa-f]{1,4}"
    };
}
macro_rules! ls32 {
    () => {
        concat!("(?:", h16!(), ":", h16!(), "|", ipv4!(), ")")
    };
}
macro_rules! ipv6 {
    () => {
        concat!(
            "(?:",
            concat!("(?:", h16!(), ":){6}", ls32!()),
            concat!("|::(?:", h16!(), ":){5}", ls32!()),
            concat!("|(?:", h16!(), ")?::(?:", h16!(), ":){4}", ls32!()),
            concat!(
                "|(?:(?:",
                h16!(),
                ":){0,1}",
                h16!(),
                ")?::(?:",
                h16!(),
                ":){3}",
                ls32!()
            ),
            concat!(
                "|(?:(?:",
                h16!(),
                ":){0,2}",
                h16!(),
                ")?::(?:",
                h16!(),
                ":){2}",
                ls32!()
            ),
            concat!(
                "|(?:(?:",
                h16!(),
                ":){0,3}",
                h16!(),
                ")?::",
                h16!(),
                ":",
                ls32!()
            ),
            concat!("|(?:(?:", h16!(), ":){0,4}", h16!(), ")?::", ls32!()),
            concat!("|(?:(?:", h16!(), ":){0,5}", h16!(), ")?::", h16!()),
            concat!("|(?:(?:", h16!(), ":){0,6}", h16!(), ")?::"),
            ")"
        )
    };
}
const IPV6: &str = whole!(ipv6!());

// RFC 3986, appendix A. `unreserved`, `sub-delims` and what a rule adds to them are one
// class, and `pct-encoded` stands next to it.
macro_rules! percent {
    () => {
        "%[0-9A-Fa-f]{2}"
    };
}
macro_rules! characters {
    ($more:literal) => {
        concat!("(?:[A-Za-z0-9._~!$&'()*+,;=", $more, "-]|", percent!(), ")")
    };
}
macro_rules! pchar {
    () => {
        characters!(":@")
    };
}
macro_rules! authority {
    () => {
        concat!(
            // userinfo
            "(?:",
            characters!(":"),
            "*@)?",
            // host: an address in brackets, or a name, which an IPv4 address is too
            r"(?:\[(?:",
            ipv6!(),
            r"|[Vv][0-9A-Fa-f]+\.[A-Za-z0-9._~!$&'()*+,;=:-]+)\]|",
            characters!(""),
            "*)",
            // port
            "(?::[0-9]*)?"
        )
    };
}
macro_rules! segments {
    () => {
        concat!("(?:/", pchar!(), "*)*")
    };
}
macro_rules! query_and_fragment {
    () => {
        concat!(
            r"(?:\?",
            characters!(":@/?"),
            "*)?(?:#",
            characters!(":@/?"),
            "*)?"
        )
    };
}
macro_rules! uri {
    () => {
        concat!(
            "[A-Za-z][A-Za-z0-9+.-]*:(?:",
            concat!("//", authority!(), segments!()),
            concat!("|/(?:", pchar!(), "+", segments!(), ")?"),
            concat!("|", pchar!(), "+", segments!()),
            "|)",
            query_and_fragment!()
        )
    };
}
const URI: &str = whole!(uri!());
const URI_REFERENCE: &str = whole!(
    uri!(),
    "|(?:",
    concat!("//", authority!(), segments!()),
    concat!("|/(?:", pchar!(), "+", segments!(), ")?"),
    // A first segment with a colon in it would read as a scheme.
    concat!("|", characters!("@"), "+", segments!()),
    "|)",
    query_and_fragment!()
);

// RFC 6901, section 3.
macro_rules! json_pointer {
    () => {
        "(?:/(?:[^/~]|~[01])*)*"
    };
}
const JSON_POINTER: &str = whole!(json_pointer!());

// The Internet-Draft draft-handrews-relative-json-pointer-01, section 3.
const RELATIVE_JSON_POINTER: &str = whole!("(?:0|[1-9][0-9]*)(?:#|", json_pointer!(), ")");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Budget;
    use crate::language::{Languages, Lengths};

    const MODELLED: [&str; 11] = [
        "date",
        "time",
        "date-time",
        "duration",
        "uuid",
        "ipv4",
        "ipv6",
        "uri",
        "uri-reference",
        "json-pointer",
        "relative-json-pointer",
    ];

    /// Holds a format against strings that it accepts and strings that it does not, as the
    /// `regex` crate reads its pattern. Of none of them the format leaves open whether it
    /// accepts it.
    fn accepts(format: &str, valid: &[&str], invalid: &[&str]) {
        let modelled = modelled(format).unwrap();
        let read = |pattern| regex::Regex::new(pattern).unwrap();
        let (accepted, open) = (read(modelled.accepted), modelled.open.map(read));
        let is_open = |string: &str| open.as_ref().is_some_and(|open| open.is_match(string));
        for string in valid {
            assert!(accepted.is_match(string), "{format} accepts {string:?}");
        }
        for string in invalid {
            assert!(!accepted.is_match(string), "{format} rejects {string:?}");
            assert!(!is_open(string), "{format} is sure of {string:?}");
        }
    }

    /// Holds a format against strings of which it leaves open whether it accepts them.
    fn leaves_open(format: &str, strings: &[&str]) {
        let modelled = modelled(format).unwrap();
        let read = |pattern| regex::Regex::new(pattern).unwrap();
        let (accepted, open) = (read(modelled.accepted), read(modelled.open.unwrap()));
        for string in strings {
            assert!(open.is_match(string), "{format} leaves {string:?} open");
            assert!(
                !accepted.is_match(string),
                "{format} is not sure of {string:?}"
            );
        }
    }

    #[test]
    fn a_format_that_is_not_modelled_has_no_pattern() {
        for format in MODELLED {
            assert!(modelled(format).is_some(), "{format}");
        }
        let others = [
            "hostname",
            "email",
            "idn-hostname",
            "idn-email",
            "iri",
            "iri-reference",
            "uri-template",
            "regex",
            "Date",
            "",
            "binary",
        ];
        for format in others {
            assert_eq!(modelled(format), None, "{format}");
        }
    }

    #[test]
    fn a_date_has_the_days_of_its_month() {
        accepts(
            "date",
            &[
                "1963-06-19",
                "2020-01-31",
                "2020-04-30",
                "2020-12-31",
                "2021-02-28",
                "2020-02-29",
                "2000-02-29",
                "0000-02-29",
                "2400-02-29",
                "1996-02-29",
                "9999-12-31",
                "0000-01-01",
            ],
            &[
                "",
                "2020-04-31",
                "2020-01-32",
                "2020-13-01",
                "2020-00-10",
                "2020-01-00",
                "2021-02-29",
                "1900-02-29",
                "2100-02-29",
                "2020-02-30",
                "1998-1-20",
                "1998-01-1",
                "06/19/1963",
                "2013-350",
                "1963-06-1\u{9ea}",
                "20200131",
                "2020-01-31 ",
                " 2020-01-31",
                "2020-01-31\n",
                "12020-01-31",
                "+2020-01-31",
            ],
        );
    }

    #[test]
    fn a_time_has_an_offset_and_its_second_60_is_left_open() {
        accepts(
            "time",
            &[
                "08:30:06Z",
                "08:30:06z",
                "08:30:06+00:20",
                "08:30:06-08:00",
                "23:20:50.52Z",
                "08:30:06.283185Z",
                "00:00:00+23:59",
                "23:59:59-23:59",
                "00:00:00.0-00:00",
            ],
            &[
                "",
                "12:00:00",
                "24:00:00Z",
                "00:60:00Z",
                "00:00:61Z",
                "01:02:03+24:00",
                "01:02:03+00:60",
                "01:02:03Z+00:30",
                "08:30:06 PST",
                "01:01:01,1111",
                "1\u{9e8}:00:00Z",
                "08:30:06.Z",
                "8:30:06Z",
                "08:30Z",
                "08:30:06+0020",
                "24:00:60Z",
                "00:60:60Z",
                "23:59:60",
                "23:59:60+24:00",
                "23:59:6Z",
                "23:59:600Z",
            ],
        );
        // Whether the second 60 is one depends on the day, which a time does not name.
        leaves_open(
            "time",
            &[
                "23:59:60Z",
                "23:59:60z",
                "23:59:60+00:00",
                "01:29:60+01:30",
                "15:59:60-08:00",
                "15:59:60.123-08:00",
                "22:59:60Z",
                "23:58:60Z",
                "23:59:60+01:00",
                "00:00:60Z",
            ],
        );
    }

    #[test]
    fn a_date_time_is_a_date_and_a_time() {
        accepts(
            "date-time",
            &[
                "1963-06-19T08:30:06.283185Z",
                "1963-06-19T08:30:06Z",
                "1937-01-01T12:00:27.87+00:20",
                "1990-12-31T15:59:50.123-08:00",
                "1963-06-19t08:30:06.283185z",
                "2020-02-29T00:00:00Z",
            ],
            &[
                "",
                "1963-06-19",
                "08:30:06Z",
                "1963-6-19T08:30:06.283185Z",
                "1963-06-1T08:30:06.283185Z",
                "1990-02-31T15:59:60.123-08:00",
                "1990-12-31T15:59:60-24:00",
                "06/19/1963 08:30:06 PST",
                "2013-350T01:01:01",
                "1963-06-19 08:30:06Z",
                "1963-06-19T08:30:06",
                "1998-12-31T23:59:61Z",
                "2021-02-29T00:00:00Z",
                "1963-06-11T0\u{9ea}:00:00Z",
                "2021-02-29T23:59:60Z",
            ],
        );
        leaves_open(
            "date-time",
            &[
                "1998-12-31T23:59:60Z",
                "1998-12-31T15:59:60.123-08:00",
                "1998-12-31T23:58:60Z",
                "1998-12-31T22:59:60Z",
                "1998-12-30t23:59:60z",
            ],
        );
    }

    #[test]
    fn a_duration_names_its_units_in_order() {
        accepts(
            "duration",
            &[
                "P4DT12H30M5S",
                "P4Y",
                "PT0S",
                "P0D",
                "P1M",
                "PT1M",
                "PT36H",
                "P1DT12H",
                "P2W",
                "P1Y2M3D",
                "P1Y2M",
                "P2M3D",
                "PT1H2M3S",
                "PT2M3S",
                "P1Y2M3DT4H5M6S",
                "P00012D",
            ],
            &[
                "",
                "P",
                "PT",
                "P1Y2W",
                "P2W1D",
                "P1WT1H",
                "PT1D",
                "P1YT",
                "P2D1Y",
                "P1D2H",
                "P2S",
                "P1Y3D",
                "PT1H3S",
                "P\u{9e8}Y",
                "P1.5D",
                "P-1D",
                "1D",
                "P1D ",
                "P1M1M",
                "PT1S1S",
                "p1y2w",
                "pt",
                "P1d2h",
                "P1\u{17f}",
                "P1\u{212a}",
            ],
        );
        // By the letter of the grammar a small letter is as good as a capital one, and
        // validators do not take it. The letters of other alphabets that are a small `s`
        // or a `k` to some are neither.
        leaves_open(
            "duration",
            &["p1d", "pt0s", "P1dT2h", "p4y", "P1Y2m3dT4h5M6s", "P2w"],
        );
        let either = regex::Regex::new(DURATION_IN_EITHER_CASE).unwrap();
        assert!(either.is_match("P1Y2M3DT4H5M6S"));
    }

    #[test]
    fn a_uuid_is_five_groups_of_hexadecimal_digits() {
        accepts(
            "uuid",
            &[
                "2EB8AA08-AA98-11EA-B4AA-73B441D16380",
                "2eb8aa08-aa98-11ea-b4aa-73b441d16380",
                "2eb8aa08-AA98-11ea-B4Aa-73B441D16380",
                "00000000-0000-0000-0000-000000000000",
                "99c17cbb-656f-f64a-940f-1a4568f03487",
            ],
            &[
                "",
                "2eb8aa08-aa98-11ea-b4aa-73b441d1638",
                "2eb8aa08-aa98-11ea-73b441d16380",
                "2eb8aa08-aa98-11ea-b4ga-73b441d16380",
                "2eb8aa08aa9811eab4aa73b441d16380",
                "2eb8-aa08-aa98-11ea-b4aa73b44-1d16380",
                "{2eb8aa08-aa98-11ea-b4aa-73b441d16380}",
                "urn:uuid:2eb8aa08-aa98-11ea-b4aa-73b441d16380",
                "2eb8aa08-aa98-11ea-b4aa-73b441d163800",
                "2eb8aa08-aa98-11ea-b4aa-73b441d1638\u{9ea}",
            ],
        );
    }

    #[test]
    fn an_ipv4_address_is_four_numbers_up_to_255() {
        accepts(
            "ipv4",
            &[
                "192.168.0.1",
                "87.10.0.1",
                "0.0.0.0",
                "255.255.255.255",
                "1.20.199.200",
            ],
            &[
                "",
                "127.0.0.0.1",
                "256.256.256.256",
                "127.0",
                "0x7f000001",
                "2130706433",
                "1\u{9e8}7.0.0.1",
                "1.2.3.",
                ".1.2.3",
                "1..2.3",
                "1.2.3.4 ",
                "300.1.1.1",
                "1.2.3.-4",
                "192.168.1.0/24",
                "0256.1.1.1",
                "0001.2.3.4",
                "1.2.3.0o7",
                "00.1.1.256",
                // By the letter of the grammar a number may have zeros before it. The
                // corpus and validators take no such address, and neither does the library.
                "087.10.0.1",
                "1.2.3.00",
                "01.2.3.4",
                "001.002.003.004",
                "000.0.0.0",
                "255.255.255.099",
            ],
        );
        // Inside an IPv6 address and a URI the number has no zero before it either.
        accepts("ipv6", &["::1.2.3.4"], &["::01.2.3.4"]);
    }

    #[test]
    fn an_ipv6_address_is_eight_groups_with_one_run_of_zeros_left_out() {
        accepts(
            "ipv6",
            &[
                "::1",
                "::",
                "::42:ff:1",
                "d6::",
                "1::d6:192.168.0.1",
                "1:2::192.168.0.1",
                "::ffff:192.168.0.1",
                "1:2:3:4:5:6:7:8",
                "1000:1000:1000:1000:1000:1000:255.255.255.255",
                "1:2:3:4:5:6:7::",
                "::2:3:4:5:6:7:8",
                "1::8",
                "1:2:3:4:5:6:1.2.3.4",
                "::1.2.3.4",
                "FE80::aBc",
                "1:2:3:4:5::1.2.3.4",
                "1::2:3:4:5:6:7",
            ],
            &[
                "",
                ":2:3:4::8",
                "1::d6::42",
                "1::2:192.168.256.1",
                "1::2:192.168.ff.1",
                "1:2:3:4:5:::8",
                "1:2:3:4:5:6:7",
                "12345::",
                "1",
                "127.0.0.1",
                "1:2:3:4:1.2.3",
                "  ::1",
                "::1  ",
                "fe80::/64",
                "fe80::a%eth1",
                "100:100:100:100:100:100:255.255.255.255.255",
                "100:100:100:100:100:100:100:255.255.255.255",
                "1:1:1:1:1:1:1:1:1",
                "1:2:3:4:5:6:7:\u{9ea}",
                "1:2::192.16\u{9ea}.0.1",
                "::laptop",
                ":2:3:4:5:6:7:8",
                "1:2:3:4:5:6:7:",
                "1:2:3:4:5:6:7:8::",
                "::1:2:3:4:5:6:7:8",
                "1::2::3",
                "1:2:3:4:5:6:7:1.2.3.4",
                "1.2.3.4::",
                "[::1]",
                "1:2:3:4:5:6::1.2.3.4",
            ],
        );
    }

    #[test]
    fn a_uri_has_a_scheme_and_a_reference_need_not() {
        let uris = [
            "http://foo.bar/?baz=qux#quux",
            "mailto:John.Doe@example.com",
            "news:comp.infosystems.www.servers.unix",
            "tel:+1-816-555-1212",
            "urn:oasis:names:specification:docbook:dtd:xml:4.1.2",
            "http://foo.com/blah_(wikipedia)_blah#cite-1",
            "http://foo.bar/?q=Test%20URL-encoded%20stuff",
            "http://xn--nw2a.xn--j6w193g/",
            "http://-.~_!$&'()*+,;=:%40:80%2f::::::@example.com",
            "http://223.255.255.254",
            "ftp://ftp.is.co.za/rfc/rfc1808.txt",
            "ldap://[2001:db8::7]/c=GB?objectClass?one",
            "a:",
            "a:/",
            "a://",
            "a:b",
            "a:/b//c",
            "a://@:/",
            "a://[v1.x]:80",
            "a:?#",
            "file:///etc/hosts",
            "x://h?#?/",
            "A+b-c.d:e",
        ];
        let references = [
            "//foo.bar/?baz=qux#quux",
            "/abc",
            "abc",
            "#fragment",
            "",
            "?q",
            "./a:b",
            "a/b:c",
            "//",
            "///",
            "a@b",
            "%41",
            "..",
            "/",
            "//[::1]:8080/x",
        ];
        let neither = [
            "\\\\WINDOWS\\fileshare",
            "#frag\\ment",
            "http:// shouldfail.com",
            ":// should fail",
            "bar,baz:foo",
            "a b",
            "%4",
            "%zz",
            "a://[::1",
            "a://[1.2.3.4]",
            "a://h:port",
            "a#b#c",
            "http://example.com/\u{e9}",
            "1a:b",
            "a://[v.x]",
            "a://[v1.]",
            "<a>",
            "a:b\n",
        ];
        accepts("uri", &uris, &references);
        accepts("uri", &[], &neither);
        accepts("uri-reference", &uris, &neither);
        accepts("uri-reference", &references, &[]);
    }

    #[test]
    fn a_json_pointer_is_tokens_after_slashes() {
        accepts(
            "json-pointer",
            &[
                "",
                "/",
                "/foo",
                "/foo/0",
                "/foo//bar",
                "/foo/bar/",
                "/a~1b",
                "/m~0n",
                "/~1~0~0~1~1",
                "/ ",
                "/c%d",
                "/e^f",
                "/i\\j",
                "/k\"l",
                "/\u{e9}/\n",
                "//",
            ],
            &[
                "a",
                "0",
                "#",
                "#/",
                "a/a",
                "/foo/bar~",
                "/~2",
                "/~-1",
                "/~~",
                "/~0~",
                "/~0/~",
                "~0",
                " /",
            ],
        );
        accepts(
            "relative-json-pointer",
            &[
                "1",
                "0",
                "0#",
                "120#",
                "0/foo/bar",
                "2/0/baz/1/zip",
                "0/",
                "10/~0",
            ],
            &[
                "",
                "/foo/bar",
                "-1/foo/bar",
                "+1/foo/bar",
                "0##",
                "01/a",
                "01#",
                "01",
                "#",
                "1#/a",
                "1a",
                "0/~",
                "\u{9ea}/a",
            ],
        );
    }

    #[test]
    fn every_pattern_is_read_as_a_language() {
        let languages = &mut Languages::default();
        let budget = &mut Budget::new(u64::MAX);
        let expected = [
            ("date", "0000-01-01"),
            ("time", "00:00:00z"),
            ("date-time", "0000-01-01t00:00:00z"),
            ("duration", "P0D"),
            ("uuid", "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa"),
            ("ipv4", "0.0.0.0"),
            ("ipv6", "::"),
            ("uri", "a:"),
            ("uri-reference", ""),
            ("json-pointer", ""),
            ("relative-json-pointer", "0"),
        ];
        for (format, shortest) in expected {
            let language = languages.format(format, modelled(format).unwrap().accepted);
            let found = languages.shortest(language, Lengths::ANY, budget).unwrap();
            assert_eq!(found.as_deref(), Some(shortest), "{format}");
            // The word is one that the `regex` crate takes too.
            accepts(format, &[shortest], &[]);
        }
        // A date is no time, and a date-time holds one of each.
        let of = |format: &str| modelled(format).unwrap();
        let date = languages.format("date", of("date").accepted);
        let time = languages.format("time", of("time").accepted);
        let both = languages.intersection(date, time, budget).unwrap();
        assert_eq!(both, Languages::NOTHING);
        let uri = languages.format("uri", of("uri").accepted);
        let reference = languages.format("uri-reference", of("uri-reference").accepted);
        assert!(languages.includes(reference, uri, budget).unwrap());
        assert!(!languages.includes(uri, reference, budget).unwrap());
    }
}
