indexing
	description	: "System's root class"
	date: "$Date$"
	revision: "$Revision$"

class
	THRUST_GAME

create
	make

feature -- Initialization

	make is
			-- Creation procedure.
		do
			--| Add your code here
		end

feature -- BON

	cluster: SIMULATION_DUMMY

feature -- Queries

feature -- Commands

feature -- Access

	animation_engine: ANIMATION_ENGINE

	entities: LINKED_LIST[ENTITY]

	info_panel: INFO_PANEL

	high_score_display: HIGH_SCORE_DISPLAY

	sound_effects: SOUND_EFFECTS

	music: MUSIC

	input_handler: INPUT_HANDLER

	physics_system: PHYSICS_SYSTEM

feature -- Element change

	set_info_panel (an_info_panel: like info_panel) is
			-- Set `info_panel' to `an_info_panel'.
		do
			info_panel := an_info_panel
		ensure
			info_panel_assigned: info_panel = an_info_panel
		end

	set_high_score_display (a_high_score_display: like high_score_display) is
			-- Set `high_score_display' to `a_high_score_display'.
		do
			high_score_display := a_high_score_display
		ensure
			high_score_display_assigned: high_score_display = a_high_score_display
		end

	set_sound_effects (a_sound_effects: like sound_effects) is
			-- Set `sound_effects' to `a_sound_effects'.
		do
			sound_effects := a_sound_effects
		ensure
			sound_effects_assigned: sound_effects = a_sound_effects
		end

	set_music (a_music: like music) is
			-- Set `music' to `a_music'.
		do
			music := a_music
		ensure
			music_assigned: music = a_music
		end

	set_animation_engine (an_animation_engine: like animation_engine) is
			-- Set `animation_engine' to `an_animation_engine'.
		do
			animation_engine := an_animation_engine
		ensure
			animation_engine_assigned: animation_engine = an_animation_engine
		end

	set_input_handler (an_input_handler: like input_handler) is
			-- Set `input_handler' to `an_input_handler'.
		do
			input_handler := an_input_handler
		ensure
			input_handler_assigned: input_handler = an_input_handler
		end

	set_physics_system (a_physics_system: like physics_system) is
			-- Set `physics_system' to `a_physics_system'.
		do
			physics_system := a_physics_system
		ensure
			physics_system_assigned: physics_system = a_physics_system
		end

invariant -- Constraints

end -- class THRUST_GAME
