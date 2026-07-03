//! Speedrun routes, one per category.
//!
//! A [`Route`] is the ordered sequence of `(phase ID, event ID)` pairs a runner passes through for
//! a given [`Category`]. The autosplitter looks up the route for the active category and splits as
//! the game reaches each event in turn.

use std::io::Write;

use anyhow::Result;
use quick_xml::events::{BytesDecl, BytesEnd, BytesStart, BytesText, Event};
use quick_xml::writer::Writer;

use super::{ENDING_VARIABLE_NAME, NEW_GAME_VARIABLE_NAME};

/// Version of the LiveSplit splits file format we generate
const SPLITS_VERSION: &str = "1.7.0";

/// LiveSplit game name
const GAME_NAME: &str = "Way of the Samurai";

/// A run category, identified by which of the game's six endings is being pursued and whether the
/// run is New Game (NG) or New Game+ (NG+).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Category {
    /// The target ending, 1-6.
    pub ending: u8,
    /// Whether this is a New Game+ run.
    pub new_game_plus: bool,
}

impl Category {
    pub const fn new(ending: u8, new_game_plus: bool) -> Self {
        Self { ending, new_game_plus }
    }

    pub fn category_name(&self) -> String {
        format!("Ending #{}", self.ending)
    }

    pub const fn mode_name(&self) -> &'static str {
        if self.new_game_plus {
            "NG+"
        } else {
            "NG"
        }
    }

    /// Event that the game starts in for this category
    pub const fn start_event(&self) -> RouteEvent {
        if self.new_game_plus {
            (0, 0)
        } else {
            (0, 2) // tutorial
        }
    }
}

/// A single event in a route, identified by its `(phase ID, event ID)`.
pub type RouteEvent = (i8, i32);

/// The ordered sequence of events for a single category.
#[derive(Debug, Clone, Copy)]
pub struct Route {
    category: Category,
    events: &'static [RouteEvent],
}

impl Route {
    pub const fn category(&self) -> Category {
        self.category
    }

    /// The events of this route, in the order they should be split on.
    pub const fn events(&self) -> &'static [RouteEvent] {
        self.events
    }

    /// Suggested name for the splits file for this route
    pub fn splits_name(&self) -> String {
        format!("{} - {} (Emulator, {})", GAME_NAME, self.category.category_name(), self.category.mode_name())
    }

    fn write_variable<W: Write>(writer: &mut Writer<W>, name: &str, value: &str) -> Result<()> {
        writer.create_element("Variable")
            .with_attributes([("name", name)])
            .write_text_content(BytesText::new(value))?;
        Ok(())
    }

    fn write_segment<W: Write>(writer: &mut Writer<W>, event: RouteEvent) -> Result<()> {
        writer.write_event(Event::Start(BytesStart::new("Segment")))?;
        writer
            .create_element("Name")
            .write_text_content(BytesText::new(&format!("Phase {} Event {}", event.0, event.1)))?;
        writer.write_event(Event::End(BytesEnd::new("Segment")))?;
        Ok(())
    }

    /// Serialize the route as LiveSplit splits XML
    pub fn to_splits(&self) -> Result<String> {
        let mut writer = Writer::new_with_indent(Vec::new(), b' ', 2);

        writer.write_event(Event::Decl(BytesDecl::new("1.0", Some("UTF-8"), None)))?;

        // <Run>
        writer.write_event(Event::Start(
            BytesStart::new("Run").with_attributes([("version", SPLITS_VERSION)]),
        ))?;

        writer.create_element("GameIcon").write_empty()?;
        writer.create_element("GameName").write_text_content(BytesText::new(GAME_NAME))?;
        writer
            .create_element("CategoryName")
            .write_text_content(BytesText::new(&self.category.category_name()))?;

        // <Metadata>
        writer.write_event(Event::Start(BytesStart::new("Metadata")))?;

        writer
            .create_element("Run")
            .with_attributes([("id", "")])
            .write_empty()?;

        // PSP not supported yet
        writer
            .create_element("Platform")
            .with_attributes([("usesEmulator", "True")])
            .write_text_content(BytesText::new("PlayStation 2"))?;

        // only Japanese versions currently supported
        writer.create_element("Region").write_text_content(BytesText::new("JPN / NTSC"))?;

        // <Variables>
        writer.write_event(Event::Start(BytesStart::new("Variables")))?;

        Self::write_variable(&mut writer, "Platform", "Emulator")?;
        Self::write_variable(&mut writer, "Mode", self.category.mode_name())?;

        writer.write_event(Event::End(BytesEnd::new("Variables")))?;
        // </Variables>

        // <CustomVariables>
        writer.write_event(Event::Start(BytesStart::new("CustomVariables")))?;

        Self::write_variable(&mut writer, ENDING_VARIABLE_NAME, &self.category.ending.to_string())?;
        Self::write_variable(&mut writer, NEW_GAME_VARIABLE_NAME, self.category.mode_name())?;

        writer.write_event(Event::End(BytesEnd::new("CustomVariables")))?;
        // </CustomVariables>

        writer.write_event(Event::End(BytesEnd::new("Metadata")))?;
        // </Metadata>

        writer.create_element("Offset").write_text_content(BytesText::new("00:00:00"))?;
        writer.create_element("AttemptCount").write_text_content(BytesText::new("0"))?;
        writer.create_element("AttemptHistory").write_empty()?;

        // <Segments>
        writer.write_event(Event::Start(BytesStart::new("Segments")))?;

        Self::write_segment(&mut writer, self.category.start_event())?;
        for event in self.events() {
            Self::write_segment(&mut writer, *event)?;
        }

        writer.write_event(Event::End(BytesEnd::new("Segments")))?;
        // </Segments>

        writer.create_element("AutoSplitterSettings").write_empty()?;

        writer.write_event(Event::End(BytesEnd::new("Run")))?;
        // </Run>

        Ok(String::from_utf8(writer.into_inner())?)
    }
}

/// All known routes.
pub static ROUTES: &[Route] = &[
    Route {
        category: Category {
            ending: 1,
            new_game_plus: false,
        },
        events: &[
            (0, 0), // Tsubohachi and Suzu at bridge
            (1, 24), // shrine
            (1, 6), // Ipponmatsu
            (1, 0), // join Kurou
            (1, 14), // Ipponmatsu
            (1, 20), // Shiretoko at shrine
            (1, 1), // Amaguri shakedown
            (2, 19), // railway
            (2, 1), // join Akadama
            (3, 8), // railway
            (3, 17), // iron foundry
            (3, 3), // bridge
            (3, 0), // Murasaki and Inokashira at shrine
            (4, 4), // bridge
            (4, 0), // iron foundry
            (4, 9), // railway
            (4, 1), // Kitcho
            (4, 12), // Hyuga at shrine
            (5, 5), // bridge
            (5, 12), // iron foundry
            (5, 10), // railway
            (5, 3), // fight government at Akadama
            (5, 20), // fight government at railway
            (5, 21), // fight government at station
            (5, 23), // fight government at bridge
            (5, 24), // Tamagawa at shrine
        ]
    },
    Route {
        category: Category {
            ending: 2,
            new_game_plus: false,
        },
        events: &[
            (0, 0),
            (1, 26),
            (1, 4),
            (1, 3),
            (2, 17),
            (2, 2),
            (3, 3),
            (3, 2),
            (3, 14),
            (3, 15),
            (3, 16),
            (3, 13),
            (4, 4),
            (4, 2),
            (4, 19),
            (5, 2),
            (5, 25),
            (5, 26),
        ],
    },
    Route {
        category: Category {
            ending: 3,
            new_game_plus: false,
        },
        events: &[
            (0, 0),
            (1, 26),
            (1, 4), // FIXME: in later versions, this is (1, 29)
            (1, 3),
            (2, 17),
            (2, 2),
            (3, 3),
            (3, 2),
            (4, 4),
            (4, 2),
            (4, 19),
            (5, 2),
            (5, 25),
            (5, 26),
        ],
    },
    Route {
        category: Category {
            ending: 5,
            new_game_plus: false,
        },
        events: &[
            (0, 0),
            (1, 26),
            (1, 4),
            (1, 3),
            (2, 17),
            (2, 2),
            (3, 3),
            (3, 2),
            (4, 4),
            (4, 0),
            (4, 9),
            (4, 1),
            (4, 12),
            (5, 5),
            (5, 12),
            (5, 10),
            (5, 1),
            (5, 13),
            (5, 14),
            (5, 15),
            (5, 16),
        ],
    },
];

/// Look up the route for a given category if one is defined.
pub fn route_for(category: Category) -> Option<&'static Route> {
    ROUTES.iter().find(|route| route.category == category)
}