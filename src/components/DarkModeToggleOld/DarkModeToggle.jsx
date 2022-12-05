import IconButton from '@mui/material/IconButton';
import PropTypes from 'prop-types';
import { dashboardLinksIconMapper } from '../../lib/icons.js';

/**
 * Toggle component for darkmode
 * @param {Object} props
 * @component
 */
const DarkModeToggle = (props) => {
	const Brightness4Icon = dashboardLinksIconMapper['brightness4'];
	const Brightness7Icon = dashboardLinksIconMapper['brightness7'];
	// const { themeMode, toggleTheme } = useThemeContext();
	const { variant, themeMode, toggleTheme } = props;
	const TextVariant = () => {
		return (
			<>
				{'common.youAreIn'} {themeMode == 'dark' ? 'common.darkMode' : 'common.lightMode'}{' '}
				<IconButton aria-label={'common.toggle'} onClick={toggleTheme} size="large">
					{themeMode === 'light' ? <Brightness7Icon /> : <Brightness4Icon />}
				</IconButton>
			</>
		);
	};
	const IconVariant = () => {
		return (
			<>
				<IconButton aria-label={'common.toggle'} onClick={toggleTheme} size="large">
					{themeMode === 'light' ? <Brightness7Icon /> : <Brightness4Icon />}
				</IconButton>
			</>
		);
	};
	return <span>{variant === 'text' ? <TextVariant /> : <IconVariant />}</span>;
};
export default DarkModeToggle;

DarkModeToggle.propTypes = {
	variant: PropTypes.string.isRequired,
	themeMode: PropTypes.string.isRequired,
	toggleTheme: PropTypes.func.isRequired,
};
