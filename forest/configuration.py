from dataclasses import dataclass


@dataclass
class Configuration:
    """ Configuration to run FOREST. """

    # Encoding used to search space:
    encoding: str = 'multitree'

    # Automatically answer questions using ground truth instead of interacting with the user.
    self_interact: bool = False

    # Path to the log file. Empty string means no log is written.
    log_path: str = ''

    # Activate/deactivate pruning
    pruning: bool = True

    # Activate/deactivate synthesis of capturing groups
    synth_captures: bool = True

    # Activate/deactivate synthesis of capture conditions
    synth_conditions: bool = True

    # Activate/deactivate disambiguation of the synthesised solutions.
    disambiguation: bool = True

    # Sketching mode.
    sketching: str = 'none'

    # Forces dynamic multitree when the encoding is multitree.
    force_dynamic: bool = False

    # Prints the first correct regex found
    print_first_regex: bool = False

    # Used in signal handling:
    die: bool = False
