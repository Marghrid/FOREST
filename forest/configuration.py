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

    # Sketching mode.
    sketching: str = 'none'

    # Forces dynamic multitree when the encoding is multitree.
    force_dynamic = False
