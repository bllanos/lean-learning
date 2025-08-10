use std::error::Error;
use std::path::Path;

use glob::MatchOptions;

pub fn find_c_files<P: AsRef<Path>>(
    lake_package_path: P,
) -> Result<impl IntoIterator<Item = String>, Box<dyn Error>> {
    let lake_package_path = lake_package_path.as_ref();
    let pattern_path = lake_package_path.join("**/*.c");
    let pattern = pattern_path.to_str().ok_or_else(|| -> Box<dyn Error> {
        format!(
            "Lake package path is not a valid UTF-8 string, \"{}\"",
            lake_package_path.display()
        )
        .into()
    })?;
    let options = MatchOptions {
        case_sensitive: true,
        require_literal_leading_dot: false,
        require_literal_separator: false,
    };
    glob::glob_with(pattern, options)?
        .map(|result| {
            result.map_err(|err| err.into()).and_then(|path| {
                path.to_str()
                    .ok_or_else(|| -> Box<dyn Error> {
                        format!(
                            "C file path is not a valid UTF-8 string, \"{}\"",
                            path.display()
                        )
                        .into()
                    })
                    .map(String::from)
            })
        })
        .collect::<Result<Vec<String>, Box<dyn Error>>>()
}
