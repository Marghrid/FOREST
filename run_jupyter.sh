ssh -J macf@aquila.inesc-id.pt macf@musca.inesc-id.pt 'cd ~/Validations-Synthesizer; source venv/bin/activate; jupyter notebook --no-browser --port=8890'
ssh -N -L localhost:8890:localhost:8890 -J macf@aquila.inesc-id.pt macf@musca.inesc-id.pt
open 'http://localhost:8890/'
