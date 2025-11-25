# systemd-unit-edit

A lossless parser and editor for systemd unit files as specified by the [systemd.syntax(7)](https://www.freedesktop.org/software/systemd/man/latest/systemd.syntax.html) and [systemd.unit(5)](https://www.freedesktop.org/software/systemd/man/latest/systemd.unit.html) specifications.

This library preserves all whitespace, comments, and formatting while providing a structured way to read and modify systemd unit files.

## Features

- **Lossless parsing**: All whitespace, comments, and formatting are preserved
- **Systemd unit file support**: Full support for the systemd unit file format
- **Line continuation support**: Handles backslash line continuations
- **Comment support**: Supports both `#` and `;` style comments
- **Multiple values**: Supports multiple entries with the same key (common in systemd)

## Example

```rust
use systemd_unit_edit::SystemdUnit;
use std::str::FromStr;

let input = r#"[Unit]
Description=Test Service
After=network.target

[Service]
Type=simple
ExecStart=/usr/bin/test
"#;

let unit = SystemdUnit::from_str(input).unwrap();

// Read sections
for section in unit.sections() {
    println!("Section: {}", section.name().unwrap());
    for entry in section.entries() {
        println!("  {} = {}", entry.key().unwrap(), entry.value().unwrap());
    }
}

// Modify values
let mut service_section = unit.get_section("Service").unwrap();
service_section.set("Type", "forking");

// Add new entries
service_section.add("ExecReload", "/bin/kill -HUP $MAINPID");

// Write back to string
println!("{}", unit);
```

## API

### SystemdUnit

The root type representing a parsed systemd unit file.

- `SystemdUnit::from_str(text)` - Parse from a string
- `SystemdUnit::from_file(path)` - Load from a file
- `unit.sections()` - Iterate over all sections
- `unit.get_section(name)` - Get a specific section by name
- `unit.add_section(name)` - Add a new section
- `unit.text()` - Convert back to string (lossless)
- `unit.write_to_file(path)` - Write to a file

### Section

Represents a section in a unit file (e.g., `[Unit]`, `[Service]`).

- `section.name()` - Get the section name
- `section.entries()` - Iterate over all entries
- `section.get(key)` - Get the first value for a key
- `section.get_all(key)` - Get all values for a key (for multi-value keys)
- `section.set(key, value)` - Set a value (replaces first occurrence)
- `section.add(key, value)` - Add a value (appends even if key exists)
- `section.remove(key)` - Remove the first entry with the key
- `section.remove_all(key)` - Remove all entries with the key

### Entry

Represents a key-value entry in a section.

- `entry.key()` - Get the key name
- `entry.value()` - Get the value (with line continuations processed)
- `entry.raw_value()` - Get the raw value as it appears in the file

## License

Apache-2.0
