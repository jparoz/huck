
    use crate::utils::assert_matches;

    use super::*;

    #[test]
    fn error_file_doesnt_exist() {
        assert_matches!(load("file/doesnt/exist.hk"), Err(Error::IO(_)))
    }

    #[cfg_attr(not(unix), ignore)]
    #[test]
    fn error_bad_file_path() {
        use std::{ffi::OsString, os::unix::prelude::OsStringExt};

        // \xC3\x28 is invalid UTF-8
        let path = OsString::from_vec(Vec::from(&b"\xC3\x28.hk"[..]));
        assert_matches!(load(path), Err(Error::BadFilePath(_)));
    }
