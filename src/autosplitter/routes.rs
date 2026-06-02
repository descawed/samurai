//! Speedrun routes, one per category.
//!
//! A [`Route`] is the ordered sequence of `(phase ID, event ID)` pairs a runner passes through for
//! a given [`Category`]. The autosplitter looks up the route for the active category and splits as
//! the game reaches each event in turn.

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
}

/// All known routes.
static ROUTES: &[Route] = &[];

/// Look up the route for a given category if one is defined.
pub fn route_for(category: Category) -> Option<&'static Route> {
    ROUTES.iter().find(|route| route.category == category)
}
